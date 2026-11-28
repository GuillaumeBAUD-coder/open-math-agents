import OMAStatements.S_arxiv_1803_02550

/-! The two-path construction follows Sk Samim Islam, arXiv:2608.20036v2. -/

namespace OMA.BroadcastCheckpoint

theorem shortestWalk_segment {V : Type*} {G : SimpleGraph V}
    (connected : G.Connected) {u v : V} (walk : G.Walk u v)
    (shortest : walk.length = G.dist u v) {i j : ℕ}
    (ordered : i ≤ j) (inRange : j ≤ walk.length) :
    G.dist (walk.getVert i) (walk.getVert j) = j - i := by
  have iInRange : i ≤ walk.length := ordered.trans inRange
  have prefixBound : G.dist u (walk.getVert i) ≤ i := by
    simpa [min_eq_left iInRange] using G.dist_le (walk.take i)
  have suffixBound : G.dist (walk.getVert j) v ≤ walk.length - j := by
    simpa using G.dist_le (walk.drop j)
  have segmentBound : G.dist (walk.getVert i) (walk.getVert j) ≤ j - i := by
    have offset : i + (j - i) = j := by omega
    have remaining : j - i ≤ walk.length - i := by omega
    simpa [offset, min_eq_left remaining] using
      G.dist_le ((walk.drop i).take (j - i))
  have firstTriangle :
      G.dist u v ≤ G.dist u (walk.getVert i) + G.dist (walk.getVert i) v :=
    connected.dist_triangle
  have secondTriangle :
      G.dist (walk.getVert i) v ≤
        G.dist (walk.getVert i) (walk.getVert j) + G.dist (walk.getVert j) v :=
    connected.dist_triangle
  omega

theorem multipacking_of_far_pair {n : ℕ} {G : SimpleGraph (Fin n)}
    (connected : G.Connected) (packing : Finset (Fin n))
    (farPair : ∀ subset ⊆ packing, 2 ≤ subset.card →
      ∃ a ∈ subset, ∃ b ∈ subset, 2 * subset.card - 1 ≤ G.dist a b) :
    OMA.S_arxiv_1803_02550.IsMultipacking G packing := by
  intro center radius positive
  let subset := packing.filter fun vertex => G.dist center vertex ≤ radius
  change subset.card ≤ radius
  by_contra! tooMany
  obtain ⟨a, aMem, b, bMem, far⟩ :=
    farPair subset (Finset.filter_subset _ _) (by omega)
  have aNear : G.dist center a ≤ radius := (Finset.mem_filter.mp aMem).2
  have bNear : G.dist center b ≤ radius := (Finset.mem_filter.mp bMem).2
  have triangle : G.dist a b ≤ G.dist center a + G.dist center b := by
    calc
      G.dist a b ≤ G.dist a center + G.dist center b := connected.dist_triangle
      _ = _ := by rw [show G.dist a center = G.dist center a from G.dist_comm]
  omega



private theorem card_le_interval {indices : Finset ℕ} {low high : ℕ}
    (bounded : ∀ i ∈ indices, low ≤ i ∧ i ≤ high) :
    indices.card ≤ high + 1 - low := by
  have subset : indices ⊆ Finset.Icc low high :=
    fun i hi => Finset.mem_Icc.mpr (bounded i hi)
  simpa using Finset.card_le_card subset

private theorem card_le_span (indices : Finset ℕ) (nonempty : indices.Nonempty) :
    indices.card ≤ indices.max' nonempty - indices.min' nonempty + 1 := by
  have smallest := indices.min'_mem nonempty
  have ordered := indices.le_max' _ smallest
  have bound := card_le_interval (indices := indices)
    (low := indices.min' nonempty) (high := indices.max' nonempty)
    (fun i hi => ⟨indices.min'_le i hi, indices.le_max' i hi⟩)
  omega

private theorem clearance_one_side (indices : Finset ℕ) (nonempty : indices.Nonempty)
    {mid last clearance : ℕ} (bounded : ∀ i ∈ indices, i ≤ last)
    (far : ∀ i ∈ indices, clearance ≤ Nat.dist mid i)
    (side : (∀ i ∈ indices, i ≤ mid) ∨ (∀ i ∈ indices, mid ≤ i)) :
    clearance + indices.card ≤ max mid (last - mid) + 1 := by
  rcases side with left | right
  · let farthest := indices.max' nonempty
    have memFarthest : farthest ∈ indices := indices.max'_mem nonempty
    have farthestLe := left farthest memFarthest
    have h := far farthest memFarthest
    rw [Nat.dist_eq_sub_of_le_right farthestLe] at h
    have count : indices.card ≤ farthest + 1 := by
      simpa using card_le_interval (indices := indices) (low := 0) (high := farthest)
        (fun i hi => ⟨Nat.zero_le i, indices.le_max' i hi⟩)
    have := le_max_left mid (last - mid)
    omega
  · let nearest := indices.min' nonempty
    have memNearest : nearest ∈ indices := indices.min'_mem nonempty
    have nearestGe := right nearest memNearest
    have h := far nearest memNearest
    rw [Nat.dist_eq_sub_of_le nearestGe] at h
    have count := card_le_interval (indices := indices) (low := nearest) (high := last)
      (fun i hi => ⟨indices.min'_le i hi, bounded i hi⟩)
    have nearestLe := bounded nearest memNearest
    have := le_max_right mid (last - mid)
    omega

private theorem clearance_both_sides (indices : Finset ℕ) (nonempty : indices.Nonempty)
    {mid clearance : ℕ} (far : ∀ i ∈ indices, clearance ≤ Nat.dist mid i)
    (left : ∃ i ∈ indices, i < mid) (right : ∃ i ∈ indices, mid < i) :
    2 * clearance + indices.card ≤ indices.max' nonempty - indices.min' nonempty + 2 := by
  let low := indices.min' nonempty
  let high := indices.max' nonempty
  have lowMem : low ∈ indices := indices.min'_mem nonempty
  have highMem : high ∈ indices := indices.max'_mem nonempty
  obtain ⟨i, hi, iLeft⟩ := left
  obtain ⟨j, hj, jRight⟩ := right
  have lowLeft : low < mid := lt_of_le_of_lt (indices.min'_le i hi) iLeft
  have highRight : mid < high := lt_of_lt_of_le jRight (indices.le_max' j hj)
  by_cases midMem : mid ∈ indices
  · have zero : clearance = 0 := by simpa [Nat.dist] using far mid midMem
    have span := card_le_span indices nonempty
    omega
  · have farLow := far low lowMem
    have farHigh := far high highMem
    rw [Nat.dist_eq_sub_of_le_right lowLeft.le] at farLow
    rw [Nat.dist_eq_sub_of_le highRight.le] at farHigh
    have covers : indices ⊆ Finset.Icc low (mid - clearance) ∪ Finset.Icc (mid + clearance) high := by
      intro a ha
      have aFar := far a ha
      rcases le_total a mid with h | h
      · rw [Nat.dist_eq_sub_of_le_right h] at aFar
        exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨indices.min'_le a ha, by omega⟩)
      · rw [Nat.dist_eq_sub_of_le h] at aFar
        exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, indices.le_max' a ha⟩)
    have count := (Finset.card_le_card covers).trans (Finset.card_union_le _ _)
    simp only [Nat.card_Icc] at count
    omega

/-- The mixed-subset count for the every-third-point construction. -/
theorem mixed_indices_impossible (R : ℕ) (positive : 0 < R)
    (I J : Finset ℕ) (iNonempty : I.Nonempty) (jNonempty : J.Nonempty)
    (iBound : ∀ i ∈ I, i ≤ R / 3) (jBound : ∀ j ∈ J, j < (R - 1) / 6)
    (samePath : ∀ i ∈ I, ∀ i' ∈ I,
      3 * Nat.dist i i' + 2 ≤ 2 * (I.card + J.card))
    (crossPath : ∀ i ∈ I, ∀ j ∈ J,
      R + 2 ≤ 3 * j + 3 * Nat.dist (R / 6) i + 2 * (I.card + J.card)) :
    False := by
  let k := R / 6
  let p := R / 3
  let ell := (R - 1) / 6
  let low := I.min' iNonempty
  let high := I.max' iNonempty
  let jFirst := J.min' jNonempty
  let radial := I.image (Nat.dist k)
  have radialNonempty : radial.Nonempty := iNonempty.image _
  let clearance := radial.min' radialNonempty
  obtain ⟨nearest, nearestMem, nearestDist⟩ :=
    Finset.mem_image.mp (radial.min'_mem radialNonempty)
  have clearanceLe : ∀ i ∈ I, clearance ≤ Nat.dist k i := by
    intro i hi
    exact radial.min'_le _ (Finset.mem_image_of_mem _ hi)
  have jFirstMem : jFirst ∈ J := J.min'_mem jNonempty
  have jCount : jFirst + J.card ≤ ell := by
    have subset : J ⊆ Finset.Ico jFirst ell :=
      fun j hj => Finset.mem_Ico.mpr ⟨J.min'_le j hj, jBound j hj⟩
    have count := Finset.card_le_card subset
    rw [Nat.card_Ico] at count
    have := jBound jFirst jFirstMem
    omega
  have cross := crossPath nearest nearestMem jFirst jFirstMem
  change Nat.dist k nearest = clearance at nearestDist
  rw [nearestDist] at cross
  have crossCount : R + J.card + 2 ≤ 3 * ell + 3 * clearance + 2 * I.card := by omega
  have iSubset : I ⊆ Finset.Iic p := fun i hi => Finset.mem_Iic.mpr (iBound i hi)
  have iCount : I.card ≤ p + 1 := by simpa [Nat.card_Iic] using Finset.card_le_card iSubset
  have jSubset : J ⊆ Finset.range ell := fun j hj => Finset.mem_range.mpr (jBound j hj)
  have jTotal : J.card ≤ ell := by simpa using Finset.card_le_card jSubset
  have iPositive := Finset.card_pos.mpr iNonempty
  have jPositive := Finset.card_pos.mpr jNonempty
  have residues : R = 6*k + R%6 := by dsimp [k]; omega
  have pValue : p = 2*k + (if R%6 < 3 then 0 else 1) := by split <;> (dsimp [p,k]; omega)
  have ellValue : ell = (if R%6 = 0 then k - 1 else k) := by split <;> (dsimp [ell,k]; omega)
  by_cases side : (∀ i ∈ I, i ≤ k) ∨ (∀ i ∈ I, k ≤ i)
  · have oneSide := clearance_one_side I iNonempty iBound clearanceLe side
    have maxValue : max k (p-k) = (if R%6 < 3 then k else k+1) := by
      by_cases h : R%6 < 3 <;> simp [h] at pValue ⊢ <;> omega
    rw [maxValue] at oneSide
    omega
  · push Not at side
    obtain ⟨⟨i, hi, iRight⟩, ⟨j, hj, jLeft⟩⟩ := side
    have spread := clearance_both_sides I iNonempty clearanceLe ⟨j,hj,jLeft⟩ ⟨i,hi,iRight⟩
    have lowMem : low ∈ I := I.min'_mem iNonempty
    have highMem : high ∈ I := I.max'_mem iNonempty
    have lowLeHigh : low ≤ high := I.le_max' _ lowMem
    have close := samePath low lowMem high highMem
    rw [Nat.dist_eq_sub_of_le lowLeHigh] at close
    have bothSides : 2 * R ≤ 6 * ell + 3 * I.card := by omega
    have remaining : (R%6 = 1 ∨ R%6 = 3) ∧ I.card = p + 1 := by omega
    have fullI : I = Finset.Iic p := Finset.eq_of_subset_of_card_le iSubset (by simp [Nat.card_Iic, remaining.2])
    have zeroMem : 0 ∈ I := by rw [fullI]; simp
    have endMem : p ∈ I := by rw [fullI]; simp
    have endpoints := samePath 0 zeroMem p endMem
    rw [Nat.dist_eq_sub_of_le (Nat.zero_le p), Nat.sub_zero, remaining.2] at endpoints
    have remainderOne : R%6 = 1 := by omega
    have jFullCard : J.card = ell := by omega
    have fullJ : J = Finset.range ell := Finset.eq_of_subset_of_card_le jSubset (by simp [jFullCard])
    have kMem : k ∈ I := by rw [fullI]; exact Finset.mem_Iic.mpr (by omega)
    have jZero : 0 ∈ J := by rw [fullJ]; exact Finset.mem_range.mpr (by omega)
    have endCross := crossPath k kMem 0 jZero
    change R + 2 ≤ 3 * 0 + 3 * Nat.dist k k + 2 * (I.card + J.card) at endCross
    rw [Nat.dist_eq_zero rfl] at endCross
    omega


private theorem image_injective_of_spacing {n : ℕ} {G : SimpleGraph (Fin n)}
    (indices : Finset ℕ) (f : ℕ → Fin n)
    (spacing : ∀ i ∈ indices, ∀ j ∈ indices, G.dist (f i) (f j) = 3 * Nat.dist i j) :
    Set.InjOn f (↑indices : Set ℕ) := by
  intro i hi j hj equal
  have far := spacing i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj)
  rw [equal, G.dist_self] at far
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le h] at far; omega
  · rw [Nat.dist_eq_sub_of_le_right h] at far; omega

private theorem far_pair_one_image {n : ℕ} {G : SimpleGraph (Fin n)}
    (indices : Finset ℕ) (f : ℕ → Fin n)
    (spacing : ∀ i ∈ indices, ∀ j ∈ indices, G.dist (f i) (f j) = 3 * Nat.dist i j)
    (large : 2 ≤ indices.card) :
    ∃ a ∈ indices.image f, ∃ b ∈ indices.image f, 3 * (indices.card - 1) ≤ G.dist a b := by
  have nonempty := Finset.card_pos.mp (by omega : 0 < indices.card)
  let low := indices.min' nonempty
  let high := indices.max' nonempty
  have lowMem : low ∈ indices := indices.min'_mem nonempty
  have highMem : high ∈ indices := indices.max'_mem nonempty
  have ordered : low ≤ high := indices.le_max' _ lowMem
  refine ⟨f low, Finset.mem_image_of_mem _ lowMem, f high, Finset.mem_image_of_mem _ highMem, ?_⟩
  rw [spacing low lowMem high highMem, Nat.dist_eq_sub_of_le ordered]
  have span : indices.card ≤ high - low + 1 := card_le_span _ nonempty
  omega

private theorem sampled_disjoint {n : ℕ} {G : SimpleGraph (Fin n)} (R : ℕ)
    (positive : 0 < R) (x z : ℕ → Fin n)
    (cross : ∀ i ≤ R / 3, ∀ j < (R - 1) / 6,
      R ≤ 3 * j + 3 * Nat.dist (R / 6) i + G.dist (x i) (z j)) :
    Disjoint ((Finset.Iic (R / 3)).image x) ((Finset.range ((R - 1) / 6)).image z) := by
  rw [Finset.disjoint_left]
  intro a hx hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, equal⟩ := Finset.mem_image.mp hz
  have iBound := Finset.mem_Iic.mp hi
  have jBound := Finset.mem_range.mp hj
  have close := cross i iBound j jBound
  rw [equal, G.dist_self] at close
  have radial : Nat.dist (R / 6) i ≤ R / 6 + 1 := by
    rcases le_total i (R / 6) with h | h
    · rw [Nat.dist_eq_sub_of_le_right h]
      omega
    · rw [Nat.dist_eq_sub_of_le h]
      omega
  omega

private theorem sampled_farPair {n : ℕ} {G : SimpleGraph (Fin n)}
    (X Z : Finset ℕ) (x z : ℕ → Fin n)
    (xDist : ∀ i ∈ X, ∀ j ∈ X, G.dist (x i) (x j) = 3 * Nat.dist i j)
    (zDist : ∀ i ∈ Z, ∀ j ∈ Z, G.dist (z i) (z j) = 3 * Nat.dist i j)
    (disjoint : Disjoint (X.image x) (Z.image z))
    (threshold : ℕ → ℕ) (minimum : ℕ) (minimumTwo : 2 ≤ minimum)
    (threshold_le : ∀ t, minimum ≤ t → threshold t ≤ 3 * (t - 1))
    (mixed : ∀ I J : Finset ℕ, I ⊆ X → J ⊆ Z → I.Nonempty → J.Nonempty →
      (∀ i ∈ I, ∀ i' ∈ I, G.dist (x i) (x i') < threshold (I.card + J.card)) →
      (∀ i ∈ I, ∀ j ∈ J, G.dist (x i) (z j) < threshold (I.card + J.card)) → False) :
    ∀ subset ⊆ X.image x ∪ Z.image z, minimum ≤ subset.card →
      ∃ a ∈ subset, ∃ b ∈ subset, threshold subset.card ≤ G.dist a b := by
  have xInjective := image_injective_of_spacing X x xDist
  have zInjective := image_injective_of_spacing Z z zDist
  intro subset inside large
  let I := X.filter fun i => x i ∈ subset
  let J := Z.filter fun j => z j ∈ subset
  have iSubset : I ⊆ X := Finset.filter_subset _ _
  have jSubset : J ⊆ Z := Finset.filter_subset _ _
  have union : I.image x ∪ J.image z = subset := by
    ext a
    constructor
    · intro h
      rcases Finset.mem_union.mp h with hx | hz
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hi).2
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp hj).2
    · intro h
      rcases Finset.mem_union.mp (inside h) with hx | hz
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi, h⟩))
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hj, h⟩))
  have iImageSubset : I.image x ⊆ subset := by
    rw [← union]
    exact Finset.subset_union_left
  have jImageSubset : J.image z ⊆ subset := by
    rw [← union]
    exact Finset.subset_union_right
  have count : subset.card = I.card + J.card := by
    rw [← union, Finset.card_union_of_disjoint (disjoint.mono
      (Finset.image_subset_image iSubset) (Finset.image_subset_image jSubset))]
    rw [Finset.card_image_of_injOn (xInjective.mono (fun _ hi => iSubset hi)),
      Finset.card_image_of_injOn (zInjective.mono (fun _ hj => jSubset hj))]
  by_cases iNonempty : I.Nonempty
  · by_cases jNonempty : J.Nonempty
    · by_contra! close
      apply mixed I J iSubset jSubset iNonempty jNonempty
      · intro i hi j hj
        rw [← count]
        exact close (x i) (iImageSubset (Finset.mem_image_of_mem _ hi))
          (x j) (iImageSubset (Finset.mem_image_of_mem _ hj))
      · intro i hi j hj
        rw [← count]
        exact close (x i) (iImageSubset (Finset.mem_image_of_mem _ hi))
          (z j) (jImageSubset (Finset.mem_image_of_mem _ hj))
    · have zero : J.card = 0 := by simpa using jNonempty
      obtain ⟨a, ha, b, hb, far⟩ := far_pair_one_image I x
        (fun i hi j hj => xDist i (iSubset hi) j (iSubset hj)) (by omega)
      have cardEq : subset.card = I.card := by omega
      rw [← cardEq] at far
      exact ⟨a, iImageSubset ha, b, iImageSubset hb, (threshold_le _ large).trans far⟩
  · have zero : I.card = 0 := by simpa using iNonempty
    obtain ⟨a, ha, b, hb, far⟩ := far_pair_one_image J z
      (fun i hi j hj => zDist i (jSubset hi) j (jSubset hj)) (by omega)
    have cardEq : subset.card = J.card := by omega
    rw [← cardEq] at far
    exact ⟨a, jImageSubset ha, b, jImageSubset hb, (threshold_le _ large).trans far⟩

/-- The base packing in Islam, arXiv:2608.20036, Lemma 2. -/
theorem baseMultipacking_from_distances {n : ℕ} {G : SimpleGraph (Fin n)}
    (connected : G.Connected) (R : ℕ) (positive : 0 < R) (x z : ℕ → Fin n)
    (xSpacing : ∀ i ≤ R / 3, ∀ j ≤ R / 3, G.dist (x i) (x j) = 3 * Nat.dist i j)
    (zSpacing : ∀ i < (R - 1) / 6, ∀ j < (R - 1) / 6,
      G.dist (z i) (z j) = 3 * Nat.dist i j)
    (cross : ∀ i ≤ R / 3, ∀ j < (R - 1) / 6,
      R ≤ 3 * j + 3 * Nat.dist (R / 6) i + G.dist (x i) (z j)) :
    let packing := (Finset.Iic (R / 3)).image x ∪ (Finset.range ((R - 1) / 6)).image z
    OMA.S_arxiv_1803_02550.IsMultipacking G packing ∧
      packing.card = R / 3 + 1 + (R - 1) / 6 := by
  let X := Finset.Iic (R / 3)
  let Z := Finset.range ((R - 1) / 6)
  let packing := X.image x ∪ Z.image z
  change OMA.S_arxiv_1803_02550.IsMultipacking G packing ∧ packing.card = _
  have xDist : ∀ i ∈ X, ∀ j ∈ X, G.dist (x i) (x j) = 3 * Nat.dist i j :=
    fun i hi j hj => xSpacing i (Finset.mem_Iic.mp hi) j (Finset.mem_Iic.mp hj)
  have zDist : ∀ i ∈ Z, ∀ j ∈ Z, G.dist (z i) (z j) = 3 * Nat.dist i j :=
    fun i hi j hj => zSpacing i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  have xInjective := image_injective_of_spacing X x xDist
  have zInjective := image_injective_of_spacing Z z zDist
  have disjoint := sampled_disjoint (G := G) R positive x z cross
  refine ⟨?_, ?_⟩
  · apply multipacking_of_far_pair connected packing
    apply sampled_farPair X Z x z xDist zDist disjoint (fun t => 2 * t - 1) 2 (by omega)
    · intro t ht
      omega
    · intro I J iSubset jSubset iNonempty jNonempty same close
      apply mixed_indices_impossible R positive I J iNonempty jNonempty
      · exact fun i hi => Finset.mem_Iic.mp (iSubset hi)
      · exact fun j hj => Finset.mem_range.mp (jSubset hj)
      · intro i hi j hj
        have h := same i hi j hj
        rw [xDist i (iSubset hi) j (iSubset hj)] at h
        omega
      · intro i hi j hj
        have h := close i hi j hj
        have bound := cross i (Finset.mem_Iic.mp (iSubset hi)) j (Finset.mem_range.mp (jSubset hj))
        omega
  · change (X.image x ∪ Z.image z).card = _
    rw [Finset.card_union_of_disjoint disjoint, Finset.card_image_of_injOn xInjective,
      Finset.card_image_of_injOn zInjective]
    simp [X, Z, Nat.card_Iic]

/-- The two sampled paths satisfy the distance bounds used in Lemmas 2, 4 and 5. -/
private theorem spacing_from_paths {n : ℕ} {G : SimpleGraph (Fin n)}
    (connected : G.Connected) (R : ℕ) (x z : ℕ → Fin n)
    (hX : ∀ i ≤ R, ∀ j ≤ R, G.dist (x i) (x j) = Nat.dist i j)
    (hZ : ∀ i ≤ R, ∀ j ≤ R, G.dist (z i) (z j) = Nat.dist i j)
    (joined : z 0 = x (3 * (R / 6))) :
    (∀ i ≤ R / 3, ∀ j ≤ R / 3,
      G.dist (x (3 * i)) (x (3 * j)) = 3 * Nat.dist i j) ∧
    (∀ i < (R - 1) / 6, ∀ j < (R - 1) / 6,
      G.dist (z (R - 3 * i)) (z (R - 3 * j)) = 3 * Nat.dist i j) ∧
    (∀ i ≤ R / 3, ∀ j < (R - 1) / 6,
      R ≤ 3 * j + 3 * Nat.dist (R / 6) i + G.dist (x (3 * i)) (z (R - 3 * j))) := by
  have xSpacing : ∀ i ≤ R / 3, ∀ j ≤ R / 3,
      G.dist (x (3 * i)) (x (3 * j)) = 3 * Nat.dist i j := by
    intro i hi j hj
    rw [hX _ (by omega) _ (by omega)]
    rcases le_total i j with h | h
    · rw [Nat.dist_eq_sub_of_le h, Nat.dist_eq_sub_of_le (by omega : 3 * i ≤ 3 * j)]
      omega
    · rw [Nat.dist_eq_sub_of_le_right h,
        Nat.dist_eq_sub_of_le_right (by omega : 3 * j ≤ 3 * i)]
      omega
  refine ⟨xSpacing, ?_, ?_⟩
  · intro i hi j hj
    rw [hZ _ (by omega) _ (by omega)]
    rcases le_total i j with h | h
    · rw [Nat.dist_eq_sub_of_le h,
        Nat.dist_eq_sub_of_le_right (by omega : R - 3 * j ≤ R - 3 * i)]
      omega
    · rw [Nat.dist_eq_sub_of_le_right h,
        Nat.dist_eq_sub_of_le (by omega : R - 3 * i ≤ R - 3 * j)]
      omega
  · intro i hi j hj
    have base := hZ 0 (Nat.zero_le _) (R - 3 * j) (Nat.sub_le _ _)
    rw [joined, Nat.dist_eq_sub_of_le (Nat.zero_le _), Nat.sub_zero] at base
    have xBound := xSpacing (R / 6) (by omega) i hi
    have triangle : G.dist (x (3 * (R / 6))) (z (R - 3 * j)) ≤
        G.dist (x (3 * (R / 6))) (x (3 * i)) + G.dist (x (3 * i)) (z (R - 3 * j)) :=
      connected.dist_triangle
    omega

theorem baseMultipacking_from_paths {n : ℕ} {G : SimpleGraph (Fin n)}
    (connected : G.Connected) (R : ℕ) (positive : 0 < R) (x z : ℕ → Fin n)
    (hX : ∀ i ≤ R, ∀ j ≤ R, G.dist (x i) (x j) = Nat.dist i j)
    (hZ : ∀ i ≤ R, ∀ j ≤ R, G.dist (z i) (z j) = Nat.dist i j)
    (joined : z 0 = x (3 * (R / 6))) :
    ∃ packing, OMA.S_arxiv_1803_02550.IsMultipacking G packing ∧
      packing.card = R / 3 + 1 + (R - 1) / 6 := by
  obtain ⟨xDist, zDist, cross⟩ := spacing_from_paths connected R x z hX hZ joined
  exact ⟨_, baseMultipacking_from_distances connected R positive _ _ xDist zDist cross⟩

private theorem mixed_exception_impossible (k : ℕ)
    (I J : Finset ℕ) (iNonempty : I.Nonempty) (jNonempty : J.Nonempty)
    (iBound : ∀ i ∈ I, i ≤ 2 * k + 1) (jBound : ∀ j ∈ J, j < k)
    (samePath : ∀ i ∈ I, ∀ i' ∈ I, 3 * Nat.dist i i' ≤ 2 * (I.card + J.card))
    (crossPath : ∀ i ∈ I, ∀ j ∈ J,
      6 * k + 5 ≤ 3 * j + 3 * Nat.dist k i + 2 * (I.card + J.card)) :
    False := by
  let radial := I.image (Nat.dist k)
  have radialNonempty := iNonempty.image (Nat.dist k)
  let clearance := radial.min' radialNonempty
  obtain ⟨nearest, nearestMem, nearestDist⟩ :=
    Finset.mem_image.mp (radial.min'_mem radialNonempty)
  have clearanceLe : ∀ i ∈ I, clearance ≤ Nat.dist k i :=
    fun i hi => radial.min'_le _ (Finset.mem_image_of_mem _ hi)
  let jFirst := J.min' jNonempty
  have jFirstMem : jFirst ∈ J := J.min'_mem jNonempty
  have jCount : jFirst + J.card ≤ k := by
    have subset : J ⊆ Finset.Ico jFirst k :=
      fun j hj => Finset.mem_Ico.mpr ⟨J.min'_le j hj, jBound j hj⟩
    have count := Finset.card_le_card subset
    rw [Nat.card_Ico] at count
    have := jBound jFirst jFirstMem
    omega
  have cross := crossPath nearest nearestMem jFirst jFirstMem
  change Nat.dist k nearest = clearance at nearestDist
  rw [nearestDist] at cross
  have crossCount : 3 * k + J.card + 5 ≤ 3 * clearance + 2 * I.card := by omega
  have iSubset : I ⊆ Finset.Iic (2 * k + 1) := fun i hi => Finset.mem_Iic.mpr (iBound i hi)
  have iCount : I.card ≤ 2 * k + 2 := by
    simpa [Nat.card_Iic] using Finset.card_le_card iSubset
  have iPositive := Finset.card_pos.mpr iNonempty
  have jPositive := Finset.card_pos.mpr jNonempty
  by_cases side : (∀ i ∈ I, i ≤ k) ∨ (∀ i ∈ I, k ≤ i)
  · have oneSide := clearance_one_side I iNonempty iBound clearanceLe side
    omega
  · push Not at side
    obtain ⟨⟨i, hi, iRight⟩, ⟨j, hj, jLeft⟩⟩ := side
    have spread := clearance_both_sides I iNonempty clearanceLe ⟨j, hj, jLeft⟩ ⟨i, hi, iRight⟩
    have lowMem := I.min'_mem iNonempty
    have highMem := I.max'_mem iNonempty
    have close := samePath _ lowMem _ highMem
    rw [Nat.dist_eq_sub_of_le (I.le_max' _ lowMem)] at close
    have fullCard : I.card = 2 * k + 2 := by omega
    have full : I = Finset.Iic (2 * k + 1) :=
      Finset.eq_of_subset_of_card_le iSubset (by simp [Nat.card_Iic, fullCard])
    have kMem : k ∈ I := by rw [full]; exact Finset.mem_Iic.mpr (by omega)
    have noClearance : clearance = 0 := by simpa [Nat.dist] using clearanceLe k kMem
    have zeroMem : 0 ∈ I := by rw [full]; simp
    have endMem : 2 * k + 1 ∈ I := by rw [full]; simp
    have endpoints := samePath 0 zeroMem (2 * k + 1) endMem
    rw [Nat.dist_eq_sub_of_le (Nat.zero_le _), Nat.sub_zero] at endpoints
    omega

private theorem exception_farPair {n : ℕ} {G : SimpleGraph (Fin n)}
    (k : ℕ) (X Z : ℕ → Fin n)
    (xDist : ∀ i ≤ 2 * k + 1, ∀ j ≤ 2 * k + 1, G.dist (X i) (X j) = 3 * Nat.dist i j)
    (zDist : ∀ i < k, ∀ j < k, G.dist (Z i) (Z j) = 3 * Nat.dist i j)
    (cross : ∀ i ≤ 2 * k + 1, ∀ j < k,
      6 * k + 5 ≤ 3 * j + 3 * Nat.dist k i + G.dist (X i) (Z j))
    (disjoint : Disjoint ((Finset.Iic (2 * k + 1)).image X) ((Finset.range k).image Z)) :
    ∀ subset ⊆ (Finset.Iic (2 * k + 1)).image X ∪ (Finset.range k).image Z, 4 ≤ subset.card →
      ∃ a ∈ subset, ∃ b ∈ subset, 2 * subset.card + 1 ≤ G.dist a b := by
  have xSpacing : ∀ i ∈ Finset.Iic (2 * k + 1), ∀ j ∈ Finset.Iic (2 * k + 1),
      G.dist (X i) (X j) = 3 * Nat.dist i j :=
    fun i hi j hj => xDist i (Finset.mem_Iic.mp hi) j (Finset.mem_Iic.mp hj)
  have zSpacing : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k,
      G.dist (Z i) (Z j) = 3 * Nat.dist i j :=
    fun i hi j hj => zDist i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  apply sampled_farPair _ _ _ _ xSpacing zSpacing disjoint (fun t => 2 * t + 1) 4 (by omega)
  · intro t ht
    omega
  · intro I J hi hj ine jne same close
    have iBound : ∀ i ∈ I, i ≤ 2 * k + 1 := fun i h => Finset.mem_Iic.mp (hi h)
    have jBound : ∀ j ∈ J, j < k := fun j h => Finset.mem_range.mp (hj h)
    apply mixed_exception_impossible k I J ine jne iBound jBound
    · intro i iMem j jMem
      have small := same i iMem j jMem
      rw [xDist i (iBound i iMem) j (iBound j jMem)] at small
      omega
    · intro i iMem j jMem
      have small := close i iMem j jMem
      have bound := cross i (iBound i iMem) j (jBound j jMem)
      omega

private theorem card_le_two_of_endpoint_options {V : Type*} [DecidableEq V]
    (subset : Finset V) (x0 x1 xLast zPrev zLast : V)
    (possible : ∀ a ∈ subset,
      a = x0 ∨ a = x1 ∨ a = xLast ∨ a = zPrev ∨ a = zLast)
    (noX0XLast : x0 ∈ subset → xLast ∉ subset)
    (noX0ZPrev : x0 ∈ subset → zPrev ∉ subset)
    (noX0ZLast : x0 ∈ subset → zLast ∉ subset)
    (noX1ZLast : zLast ∈ subset → x1 ∉ subset)
    (noXLastZPrev : xLast ∈ subset → zPrev ∉ subset) :
    subset.card ≤ 2 := by
  have bound (a b : V) (included : ∀ c ∈ subset, c = a ∨ c = b) : subset.card ≤ 2 :=
    (Finset.card_le_card (show subset ⊆ {a, b} by
      intro c hc
      simpa using included c hc)).trans Finset.card_le_two
  by_cases x0Mem : x0 ∈ subset
  · apply bound x0 x1
    intro a ha
    have noLast := noX0XLast x0Mem
    have noPrev := noX0ZPrev x0Mem
    have noZ := noX0ZLast x0Mem
    rcases possible a ha with rfl | rfl | rfl | rfl | rfl <;> aesop
  · by_cases lastMem : xLast ∈ subset
    · have noPrev := noXLastZPrev lastMem
      by_cases zLastMem : zLast ∈ subset
      · apply bound xLast zLast
        intro a ha
        have noX1 := noX1ZLast zLastMem
        rcases possible a ha with rfl | rfl | rfl | rfl | rfl <;> aesop
      · apply bound x1 xLast
        intro a ha
        rcases possible a ha with rfl | rfl | rfl | rfl | rfl <;> aesop
    · by_cases zLastMem : zLast ∈ subset
      · apply bound zPrev zLast
        intro a ha
        have noX1 := noX1ZLast zLastMem
        rcases possible a ha with rfl | rfl | rfl | rfl | rfl <;> aesop
      · apply bound x1 zPrev
        intro a ha
        rcases possible a ha with rfl | rfl | rfl | rfl | rfl <;> aesop

/-- If a small ball contains the extra vertex in Islam's construction,
    it cannot contain as many sampled vertices as its radius. -/
private theorem exception_small_card {n : ℕ} {G : SimpleGraph (Fin n)}
    (k : ℕ) (positive : 0 < k) (X Z : ℕ → Fin n) (b : Fin n)
    (xDist : ∀ i ≤ 2 * k + 1, ∀ j ≤ 2 * k + 1, G.dist (X i) (X j) = 3 * Nat.dist i j)
    (cross : ∀ i ≤ 2 * k + 1, ∀ j < k,
      6 * k + 5 ≤ 3 * j + 3 * Nat.dist k i + G.dist (X i) (Z j))
    (xFar : ∀ i ≤ 2 * k + 1, 3 * k + 6 ≤ G.dist b (X i) + 3 * Nat.dist (k + 1) i)
    (zFar : ∀ j < k, 3 * k ≤ G.dist b (Z j) + 3 * j)
    (subset : Finset (Fin n))
    (within : subset ⊆ (Finset.Iic (2 * k + 1)).image X ∪ (Finset.range k).image Z)
    (r : ℕ) (rPos : 1 ≤ r) (rSmall : r ≤ 3)
    (nearB : ∀ a ∈ subset, G.dist b a ≤ 2 * r)
    (nearPairs : ∀ a ∈ subset, ∀ c ∈ subset, G.dist a c ≤ 2 * r) :
    subset.card < r := by
  have classify (a : Fin n) (ha : a ∈ subset) :
      (∃ i ≤ 2 * k + 1, X i = a) ∨ (∃ j < k, Z j = a) := by
    rcases Finset.mem_union.mp (within ha) with hx | hz
    · obtain ⟨i, hi, equal⟩ := Finset.mem_image.mp hx
      exact Or.inl ⟨i, Finset.mem_Iic.mp hi, equal⟩
    · obtain ⟨j, hj, equal⟩ := Finset.mem_image.mp hz
      exact Or.inr ⟨j, Finset.mem_range.mp hj, equal⟩
  have crossZeroLast := cross 0 (by omega) (k - 1) (by omega)
  rw [Nat.dist_eq_sub_of_le_right (Nat.zero_le _), Nat.sub_zero] at crossZeroLast
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl
  · have empty : subset = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro a ha
      have close := nearB a ha
      rcases classify a ha with ⟨i, hi, equal⟩ | ⟨j, hj, equal⟩
      · rw [← equal] at close
        have h := xFar i hi
        rcases le_total i (k + 1) with le | ge
        · rw [Nat.dist_eq_sub_of_le_right le] at h
          omega
        · rw [Nat.dist_eq_sub_of_le ge] at h
          omega
      · rw [← equal] at close
        have h := zFar j hj
        omega)
    simp [empty]
  · have twoOptions : ∀ a ∈ subset, a = X 0 ∨ a = Z (k - 1) := by
      intro a ha
      have close := nearB a ha
      rcases classify a ha with ⟨i, hi, equal⟩ | ⟨j, hj, equal⟩
      · rw [← equal] at close
        have h := xFar i hi
        have index : i = 0 := by
          rcases le_total i (k + 1) with le | ge
          · rw [Nat.dist_eq_sub_of_le_right le] at h
            omega
          · rw [Nat.dist_eq_sub_of_le ge] at h
            omega
        exact Or.inl (index ▸ equal.symm)
      · rw [← equal] at close
        have h := zFar j hj
        have index : j = k - 1 := by omega
        exact Or.inr (index ▸ equal.symm)
    have count : subset.card ≤ 1 := Finset.card_le_one.mpr (by
      intro a ha c hc
      rcases twoOptions a ha with rfl | rfl <;> rcases twoOptions c hc with rfl | rfl
      · rfl
      · have h := nearPairs _ ha _ hc
        omega
      · have h := nearPairs _ hc _ ha
        omega
      · rfl)
    omega
  · let xLast := X (2 * k + 1)
    let zLast := Z (k - 1)
    let zPrev := Z (k - 2)
    have x0Last := xDist 0 (by omega) (2 * k + 1) (by omega)
    rw [Nat.dist_eq_sub_of_le (Nat.zero_le _), Nat.sub_zero] at x0Last
    have crossOneLast := cross 1 (by omega) (k - 1) (by omega)
    rw [Nat.dist_eq_sub_of_le_right (by omega : 1 ≤ k)] at crossOneLast
    have crossZeroPrev := cross 0 (by omega) (k - 2) (by omega)
    rw [Nat.dist_eq_sub_of_le_right (Nat.zero_le _), Nat.sub_zero] at crossZeroPrev
    have crossLastPrev := cross (2 * k + 1) (by omega) (k - 2) (by omega)
    rw [Nat.dist_eq_sub_of_le (by omega : k ≤ 2 * k + 1)] at crossLastPrev
    by_cases size : 2 ≤ k
    · apply Nat.lt_of_le_of_lt _ (by decide : 2 < 3)
      apply card_le_two_of_endpoint_options subset (X 0) (X 1) xLast zPrev zLast
      · intro a ha
        have close := nearB a ha
        rcases classify a ha with ⟨i, hi, equal⟩ | ⟨j, hj, equal⟩
        · rw [← equal] at close
          have h := xFar i hi
          have options : i = 0 ∨ i = 1 ∨ i = 2 * k + 1 := by
            rcases le_total i (k + 1) with le | ge
            · rw [Nat.dist_eq_sub_of_le_right le] at h
              omega
            · rw [Nat.dist_eq_sub_of_le ge] at h
              omega
          rcases options with rfl | rfl | rfl <;> aesop
        · rw [← equal] at close
          have h := zFar j hj
          have options : j = k - 2 ∨ j = k - 1 := by omega
          rcases options with rfl | rfl <;> aesop
      · intro h0 hEnd
        have close := nearPairs _ h0 _ hEnd
        change G.dist (X 0) (X (2 * k + 1)) ≤ 6 at close
        omega
      · intro h0 hPrev
        have close := nearPairs _ h0 _ hPrev
        change G.dist (X 0) (Z (k - 2)) ≤ 6 at close
        omega
      · intro h0 hLast
        have close := nearPairs _ h0 _ hLast
        change G.dist (X 0) (Z (k - 1)) ≤ 6 at close
        omega
      · intro hLast h1
        have close := nearPairs _ h1 _ hLast
        change G.dist (X 1) (Z (k - 1)) ≤ 6 at close
        omega
      · intro hEnd hPrev
        have close := nearPairs _ hEnd _ hPrev
        change G.dist (X (2 * k + 1)) (Z (k - 2)) ≤ 6 at close
        omega
    · have one : k = 1 := by omega
      have fourOptions : ∀ a ∈ subset, a = X 0 ∨ a = X 1 ∨ a = xLast ∨ a = zLast := by
        intro a ha
        have close := nearB a ha
        rcases classify a ha with ⟨i, hi, equal⟩ | ⟨j, hj, equal⟩
        · rw [← equal] at close
          have h := xFar i hi
          have options : i = 0 ∨ i = 1 ∨ i = 2 * k + 1 := by
            rcases le_total i (k + 1) with le | ge
            · rw [Nat.dist_eq_sub_of_le_right le] at h
              omega
            · rw [Nat.dist_eq_sub_of_le ge] at h
              omega
          rcases options with rfl | rfl | rfl <;> aesop
        · have index : j = k - 1 := by omega
          refine Or.inr (Or.inr (Or.inr ?_))
          change a = Z (k - 1)
          rw [← index]
          exact equal.symm
      have bound (a c : Fin n) (included : ∀ v ∈ subset, v = a ∨ v = c) : subset.card < 3 :=
        ((Finset.card_le_card (show subset ⊆ {a, c} by
          intro v hv
          simpa using included v hv)).trans Finset.card_le_two).trans_lt (by decide)
      by_cases h0 : X 0 ∈ subset
      · have noXLast : xLast ∉ subset := by
          intro hEnd
          have close := nearPairs _ h0 _ hEnd
          change G.dist (X 0) (X (2 * k + 1)) ≤ 6 at close
          omega
        have noZLast : zLast ∉ subset := by
          intro hLast
          have close := nearPairs _ h0 _ hLast
          change G.dist (X 0) (Z (k - 1)) ≤ 6 at close
          omega
        apply bound (X 0) (X 1)
        intro a ha
        rcases fourOptions a ha with rfl | rfl | rfl | rfl <;> aesop
      · by_cases hLast : zLast ∈ subset
        · have noX1 : X 1 ∉ subset := by
            intro h1
            have close := nearPairs _ h1 _ hLast
            change G.dist (X 1) (Z (k - 1)) ≤ 6 at close
            omega
          apply bound xLast zLast
          intro a ha
          rcases fourOptions a ha with rfl | rfl | rfl | rfl <;> aesop
        · apply bound (X 1) xLast
          intro a ha
          rcases fourOptions a ha with rfl | rfl | rfl | rfl <;> aesop

/-- Islam, arXiv:2608.20036, Lemma 5, in terms of the registered multipacking predicate. -/
theorem extendMultipacking_from_paths {n : ℕ} {G : SimpleGraph (Fin n)}
    (connected : G.Connected) (k : ℕ) (positive : 0 < k) (x z : ℕ → Fin n)
    (hX : ∀ i ≤ 6 * k + 5, ∀ j ≤ 6 * k + 5, G.dist (x i) (x j) = Nat.dist i j)
    (hZ : ∀ i ≤ 6 * k + 5, ∀ j ≤ 6 * k + 5, G.dist (z i) (z j) = Nat.dist i j)
    (joined : z 0 = x (3 * k)) (b : Fin n)
    (bOutsideX : 3 * k + 5 < G.dist b (x (3 * k + 3)))
    (bOutsideZ : 3 * k - 1 < G.dist b (z (6 * k + 5))) :
    ∃ packing, OMA.S_arxiv_1803_02550.IsMultipacking G packing ∧
      packing.card = 3 * k + 3 := by
  let R := 6 * k + 5
  let X := fun i => x (3 * i)
  let Z := fun j => z (R - 3 * j)
  let packing := (Finset.Iic (2 * k + 1)).image X ∪ (Finset.range k).image Z
  have rPositive : 0 < R := by dsimp [R]; omega
  have divThree : R / 3 = 2 * k + 1 := by dsimp [R]; omega
  have divSix : R / 6 = k := by dsimp [R]; omega
  have divTail : (R - 1) / 6 = k := by dsimp [R]; omega
  have joined' : z 0 = x (3 * (R / 6)) := by simpa [divSix] using joined
  obtain ⟨xSpacing, zSpacing, crossSpacing⟩ := spacing_from_paths connected R x z hX hZ joined'
  have base := baseMultipacking_from_distances connected R rPositive X Z xSpacing zSpacing crossSpacing
  have disjoint := sampled_disjoint R rPositive X Z crossSpacing
  rw [divThree, divTail] at base disjoint
  change OMA.S_arxiv_1803_02550.IsMultipacking G packing ∧ packing.card = _ at base
  have xDist : ∀ i ≤ 2 * k + 1, ∀ j ≤ 2 * k + 1,
      G.dist (X i) (X j) = 3 * Nat.dist i j := by
    simpa only [X, divThree] using xSpacing
  have zDist : ∀ i < k, ∀ j < k, G.dist (Z i) (Z j) = 3 * Nat.dist i j := by
    simpa only [Z, divTail] using zSpacing
  have cross : ∀ i ≤ 2 * k + 1, ∀ j < k,
      6 * k + 5 ≤ 3 * j + 3 * Nat.dist k i + G.dist (X i) (Z j) := by
    simpa only [X, Z, divThree, divTail, divSix] using crossSpacing
  have strong := exception_farPair k X Z xDist zDist cross disjoint
  have bFarX : 3 * k + 6 ≤ G.dist b (X (k + 1)) := by
    have center : X (k + 1) = x (3 * k + 3) := rfl
    rw [center]
    omega
  have bFarZ : 3 * k ≤ G.dist b (Z 0) := by
    change 3 * k ≤ G.dist b (z (R - 3 * 0))
    simp only [Nat.mul_zero, Nat.sub_zero]
    change 3 * k ≤ G.dist b (z (6 * k + 5))
    omega
  have xFar : ∀ i ≤ 2 * k + 1, 3 * k + 6 ≤ G.dist b (X i) + 3 * Nat.dist (k + 1) i := by
    intro i hi
    have triangle : G.dist b (X (k + 1)) ≤ G.dist b (X i) + G.dist (X i) (X (k + 1)) :=
      connected.dist_triangle
    rw [xDist i hi (k + 1) (by omega), Nat.dist_comm i (k + 1)] at triangle
    exact bFarX.trans triangle
  have zFar : ∀ j < k, 3 * k ≤ G.dist b (Z j) + 3 * j := by
    intro j hj
    have triangle : G.dist b (Z 0) ≤ G.dist b (Z j) + G.dist (Z j) (Z 0) :=
      connected.dist_triangle
    rw [zDist j hj 0 positive, Nat.dist_eq_sub_of_le_right (Nat.zero_le _), Nat.sub_zero] at triangle
    exact bFarZ.trans triangle
  have notInPacking : b ∉ packing := by
    intro h
    rcases Finset.mem_union.mp h with hx | hz
    · obtain ⟨i, hi, equal⟩ := Finset.mem_image.mp hx
      have bounded := Finset.mem_Iic.mp hi
      have far := xFar i bounded
      rw [equal, G.dist_self] at far
      rcases le_total i (k + 1) with le | ge
      · rw [Nat.dist_eq_sub_of_le_right le] at far
        omega
      · rw [Nat.dist_eq_sub_of_le ge] at far
        omega
    · obtain ⟨j, hj, equal⟩ := Finset.mem_image.mp hz
      have bounded := Finset.mem_range.mp hj
      have far := zFar j bounded
      rw [equal, G.dist_self] at far
      omega
  refine ⟨insert b packing, ?_, ?_⟩
  · intro center r rPositive
    let subset := packing.filter fun a => G.dist center a ≤ r
    change ((insert b packing).filter fun a => G.dist center a ≤ r).card ≤ r
    have count : subset.card ≤ r := base.1 center r rPositive
    have within : subset ⊆ packing := Finset.filter_subset _ _
    have nearPair {a c : Fin n} (ha : G.dist center a ≤ r) (hc : G.dist center c ≤ r) :
        G.dist a c ≤ 2 * r := by
      have triangle : G.dist a c ≤ G.dist a center + G.dist center c := connected.dist_triangle
      rw [show G.dist a center = G.dist center a from G.dist_comm] at triangle
      omega
    rw [Finset.filter_insert]
    by_cases bNear : G.dist center b ≤ r
    · rw [if_pos bNear]
      change (insert b subset).card ≤ r
      rw [Finset.card_insert_of_notMem (fun h => notInPacking (within h))]
      suffices subset.card < r by omega
      by_cases large : 4 ≤ subset.card
      · obtain ⟨a, ha, c, hc, far⟩ := strong subset within large
        have close := nearPair (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hc).2
        omega
      · by_contra! fail
        have rSmall : r ≤ 3 := by omega
        have h := exception_small_card k positive X Z b xDist cross xFar zFar
          subset within r rPositive rSmall
          (fun _ ha => nearPair bNear (Finset.mem_filter.mp ha).2)
          (fun _ ha _ hc => nearPair (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hc).2)
        omega
    · rw [if_neg bNear]
      exact count
  · rw [Finset.card_insert_of_notMem notInPacking, base.2]
    omega


end OMA.BroadcastCheckpoint

namespace OMA.BroadcastAssembly

open Finset
open OMA.S_arxiv_1803_02550 (IsDominatingBroadcast IsMultipacking broadcastNumber multipackingNumber)

def IsometricPrefix {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (x : ℕ → Fin n) : Prop :=
  ∀ i j : ℕ, i ≤ j → j ≤ r → G.dist (x i) (x j) = j - i

theorem IsometricPrefix.natDist {n : ℕ} {G : SimpleGraph (Fin n)} {r : ℕ} {x : ℕ → Fin n}
    (hx : IsometricPrefix G r x) (i : ℕ) (hi : i ≤ r) (j : ℕ) (hj : j ≤ r) :
    G.dist (x i) (x j) = Nat.dist i j := by
  rcases le_total i j with hij | hji
  · simpa [Nat.dist_eq_sub_of_le hij] using hx i j hij hj
  · rw [show G.dist (x i) (x j) = G.dist (x j) (x i) from G.dist_comm]
    simpa [Nat.dist_eq_sub_of_le_right hji] using hx j i hji hi

def BasePacking {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (x z : ℕ → Fin n),
    IsometricPrefix G r x → IsometricPrefix G r z → z 0 = x (3 * (r / 6)) →
    ∃ P : Finset (Fin n), IsMultipacking G P ∧
      r ≤ 2 * P.card + 1 ∧ (r % 6 ≠ 5 → r ≤ 2 * P.card)

def ExceptionalPacking {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (x z : ℕ → Fin n) (b : Fin n),
    IsometricPrefix G (6 * k + 5) x → IsometricPrefix G (6 * k + 5) z →
    z 0 = x (3 * k) →
    3 * k + 6 ≤ G.dist b (x (3 * k + 3)) →
    3 * k ≤ G.dist b (z (6 * k + 5)) →
    ∃ P : Finset (Fin n), IsMultipacking G P ∧ 6 * k + 5 ≤ 2 * P.card

theorem base_size (r : ℕ) (pos : 0 < r) :
    r ≤ 2 * (r / 3 + 1 + (r - 1) / 6) + 1 ∧
      (r % 6 ≠ 5 → r ≤ 2 * (r / 3 + 1 + (r - 1) / 6)) := by
  constructor <;> omega

private theorem broadcast_le_cost {n : ℕ} {G : SimpleGraph (Fin n)} {f : Fin n → ℕ}
    (h : IsDominatingBroadcast G f) : broadcastNumber G ≤ ∑ v, f v :=
  csInf_le (OrderBot.bddBelow _) ⟨f, h, rfl⟩

private theorem packing_card_le {n : ℕ} {G : SimpleGraph (Fin n)} {P : Finset (Fin n)}
    (h : IsMultipacking G P) : P.card ≤ multipackingNumber G := by
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro k ⟨Q, _, rfl⟩
    simpa using card_le_univ Q
  · exact ⟨P, h, rfl⟩

private theorem broadcast_le_single {n : ℕ} {G : SimpleGraph (Fin n)}
    (c : Fin n) (r : ℕ) (positive : 0 < r) (covers : ∀ v, G.dist v c ≤ r) :
    broadcastNumber G ≤ r := by
  let f : Fin n → ℕ := fun v => if v = c then r else 0
  have h : IsDominatingBroadcast G f := by
    intro u
    exact ⟨c, by simpa [f] using positive, by simpa [f] using covers u⟩
  simpa [f] using broadcast_le_cost h

private theorem broadcast_le_two {n : ℕ} {G : SimpleGraph (Fin n)}
    (a b : Fin n) (ra rb : ℕ) (ha : 0 < ra) (hb : 0 < rb)
    (covers : ∀ v, G.dist v a ≤ ra ∨ G.dist v b ≤ rb) :
    broadcastNumber G ≤ ra + rb := by
  let f : Fin n → ℕ := fun v => (if v = a then ra else 0) + (if v = b then rb else 0)
  have fa : ra ≤ f a := by simp [f]
  have fb : rb ≤ f b := by simp [f]
  have h : IsDominatingBroadcast G f := by
    intro v
    rcases covers v with va | vb
    · exact ⟨a, ha.trans_le fa, va.trans fa⟩
    · exact ⟨b, hb.trans_le fb, vb.trans fb⟩
  simpa [f, sum_add_distrib] using broadcast_le_cost h

private theorem far_from_two {n : ℕ} {G : SimpleGraph (Fin n)}
    (a b : Fin n) (ra rb : ℕ) (ha : 0 < ra) (hb : 0 < rb)
    (h : ra + rb < broadcastNumber G) :
    ∃ v, ra + 1 ≤ G.dist v a ∧ rb + 1 ≤ G.dist v b := by
  by_contra! noFar
  have covers (v : Fin n) : G.dist v a ≤ ra ∨ G.dist v b ≤ rb := by
    by_cases h' : G.dist v a ≤ ra
    · exact Or.inl h'
    · exact Or.inr (by have := noFar v (by omega); omega)
  exact (not_le_of_gt h) (broadcast_le_two a b ra rb ha hb covers)

private theorem singleton_packing {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    IsMultipacking G {u} := by
  intro v r hr
  have h := card_le_card (filter_subset (fun w => G.dist v w ≤ r) ({u} : Finset (Fin n)))
  simpa using h.trans (by simpa using hr)

private theorem small_exception {n : ℕ} {G : SimpleGraph (Fin n)} (conn : G.Connected)
    {u v : Fin n} (huv : G.dist u v = 5) (hcost : broadcastNumber G = 5) :
    broadcastNumber G ≤ 2 * multipackingNumber G := by
  obtain ⟨b, hbu, hbv⟩ := far_from_two (G := G) u v 2 2 (by decide) (by decide) (by omega)
  let P : Finset (Fin n) := {u, v, b}
  have uv : u ≠ v := by rintro rfl; simp at huv
  have bu : b ≠ u := by rintro rfl; simp at hbu
  have bv : b ≠ v := by rintro rfl; simp at hbv
  have size : P.card = 3 := by simp [P, uv, Ne.symm bu, Ne.symm bv]
  have pack : IsMultipacking G P := by
    intro w r hr
    let Q := P.filter fun t => G.dist w t ≤ r
    change Q.card ≤ r
    have inside {a : Fin n} (ha : a ∈ Q) : G.dist w a ≤ r := (mem_filter.mp ha).2
    have close (a b : Fin n) (ha : a ∈ Q) (hb : b ∈ Q) : G.dist a b ≤ 2 * r := by
      have tri : G.dist a b ≤ G.dist a w + G.dist w b := conn.dist_triangle
      rw [show G.dist a w = G.dist w a from G.dist_comm] at tri
      have aa := inside ha
      have bb := inside hb
      omega
    by_cases large : 3 ≤ r
    · exact (card_le_card (filter_subset _ _)).trans (size.le.trans large)
    interval_cases r
    · apply card_le_one.mpr
      intro a aQ d dQ
      have da : G.dist a d ≤ 2 := close a d aQ dQ
      have aP : a = u ∨ a = v ∨ a = b := by simpa [P] using (mem_filter.mp aQ).1
      have dP : d = u ∨ d = v ∨ d = b := by simpa [P] using (mem_filter.mp dQ).1
      have hub : 3 ≤ G.dist u b := by rw [show G.dist u b = G.dist b u from G.dist_comm]; exact hbu
      have hvb : 3 ≤ G.dist v b := by rw [show G.dist v b = G.dist b v from G.dist_comm]; exact hbv
      have hvu : G.dist v u = 5 := by rw [show G.dist v u = G.dist u v from G.dist_comm, huv]
      rcases aP with rfl | rfl | rfl <;> rcases dP with rfl | rfl | rfl <;>
        first | rfl | omega
    · by_cases uQ : u ∈ Q
      · have vQ : v ∉ Q := by
          intro hv
          have := close u v uQ hv
          omega
        have sub : Q ⊆ ({u, b} : Finset (Fin n)) := by
          intro a ha
          have aP : a = u ∨ a = v ∨ a = b := by simpa [P] using (mem_filter.mp ha).1
          rcases aP with rfl | rfl | rfl
          · simp
          · exact (vQ ha).elim
          · simp
        exact (card_le_card sub).trans (by simp [Ne.symm bu])
      · have sub : Q ⊆ ({v, b} : Finset (Fin n)) := by
          intro a ha
          have aP : a = u ∨ a = v ∨ a = b := by simpa [P] using (mem_filter.mp ha).1
          rcases aP with rfl | rfl | rfl
          · exact (uQ ha).elim
          · simp
          · simp
        exact (card_le_card sub).trans (by simp [Ne.symm bv])
  have lower := packing_card_le pack
  omega

private theorem eccentricity_min {n : ℕ} {G : SimpleGraph (Fin n)} (conn : G.Connected) :
    ∃ (r : ℕ) (c : Fin n), (∀ v, G.dist v c ≤ r) ∧ ∀ v, ∃ w, r ≤ G.dist v w := by
  let ecc (v : Fin n) : ℕ := univ.sup (G.dist v)
  have hn : (univ : Finset (Fin n)).Nonempty := by
    obtain ⟨v⟩ := conn.nonempty
    exact ⟨v, mem_univ v⟩
  let values := univ.image ecc
  have hvalues : values.Nonempty := hn.image ecc
  let r := values.min' hvalues
  obtain ⟨c, _, hc⟩ := mem_image.mp (values.min'_mem hvalues)
  refine ⟨r, c, ?_, ?_⟩
  · intro v
    change G.dist v c ≤ values.min' hvalues
    rw [show G.dist v c = G.dist c v from G.dist_comm, ← hc]
    exact le_sup (f := G.dist c) (mem_univ v)
  · intro v
    have hmin : r ≤ ecc v := values.min'_le _ (mem_image_of_mem _ (mem_univ v))
    obtain ⟨w, _, hw⟩ := sup_mem_of_nonempty (f := G.dist v) hn
    exact ⟨w, hw.symm ▸ hmin⟩

private theorem prefix_exists {n : ℕ} {G : SimpleGraph (Fin n)} (conn : G.Connected)
    (r : ℕ) (u : Fin n) (far : ∃ v, r ≤ G.dist u v) :
    ∃ x : ℕ → Fin n, x 0 = u ∧ IsometricPrefix G r x := by
  obtain ⟨v, hv⟩ := far
  obtain ⟨p, hp⟩ := conn.exists_walk_length_eq_dist u v
  refine ⟨p.getVert, by simp, ?_⟩
  intro i j ordered bound
  exact OMA.BroadcastCheckpoint.shortestWalk_segment conn p hp ordered (bound.trans (hp ▸ hv))

theorem registered_from_two_path_packings {n : ℕ} (G : SimpleGraph (Fin n))
    (conn : G.Connected) (base : BasePacking G) (exceptional : ExceptionalPacking G) :
    broadcastNumber G ≤ 2 * multipackingNumber G := by
  obtain ⟨r, c, covers, far⟩ := eccentricity_min conn
  by_cases hr : r = 0
  · have up := broadcast_le_single c 1 (by decide) (fun v => (covers v).trans (by omega))
    have low := packing_card_le (singleton_packing G c)
    simp only [card_singleton] at low
    omega
  have pos : 0 < r := Nat.pos_of_ne_zero hr
  have up := broadcast_le_single c r pos covers
  obtain ⟨x, _, xIso⟩ := prefix_exists conn r c (far c)
  obtain ⟨z, start, zIso⟩ := prefix_exists conn r (x (3 * (r / 6))) (far _)
  obtain ⟨P, pack, weak, strong⟩ := base r pos x z xIso zIso start
  have low := packing_card_le pack
  by_cases mod : r % 6 = 5
  · by_cases eqr : broadcastNumber G = r
    · let k := r / 6
      have rk : r = 6 * k + 5 := by dsimp [k]; omega
      by_cases hk : k = 0
      · have r5 : r = 5 := by omega
        apply small_exception conn (u := x 0) (v := x r)
        · simpa [r5] using xIso 0 r (Nat.zero_le _) le_rfl
        · omega
      · obtain ⟨b, ba, bz⟩ := far_from_two (G := G) (x (3 * k + 3)) (z r) (3 * k + 5) (3 * k - 1)
          (by omega) (by omega) (by omega)
        have ba' : 3 * k + 6 ≤ G.dist b (x (3 * k + 3)) := by omega
        have bz' : 3 * k ≤ G.dist b (z (6 * k + 5)) := by
          rw [← rk]
          omega
        obtain ⟨Q, qPack, enough⟩ :=
          exceptional k (Nat.pos_of_ne_zero hk) x z b (rk ▸ xIso) (rk ▸ zIso) start ba' bz'
        have := packing_card_le qPack
        omega
    · omega
  · have := strong mod
    omega

end OMA.BroadcastAssembly


theorem OMA.solution : type_of% @OMA.S_arxiv_1803_02550.main := by
  intro n G conn
  apply OMA.BroadcastAssembly.registered_from_two_path_packings G conn
  · intro r positive x z xIso zIso joined
    obtain ⟨P, pack, size⟩ := OMA.BroadcastCheckpoint.baseMultipacking_from_paths
      conn r positive x z xIso.natDist zIso.natDist joined
    refine ⟨P, pack, ?_⟩
    rw [size]
    exact OMA.BroadcastAssembly.base_size r positive
  · intro k positive x z b xIso zIso joined bFarX bFarZ
    obtain ⟨P, pack, size⟩ := OMA.BroadcastCheckpoint.extendMultipacking_from_paths
      conn k positive x z xIso.natDist zIso.natDist joined b (by omega) (by omega)
    exact ⟨P, pack, by omega⟩
