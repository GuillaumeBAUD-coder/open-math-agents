import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H1: hypothesis H1 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @marcusbuffett
-- H1 := ∀ n : ℕ,     (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2       else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4) ≤       ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2  -- If no distance occurs more than n times, the bound B(n) holds (no convexity needed).

/-!
The squared chord length for a cyclic gap k is 2 − 2 cos(2πk/n).
It increases strictly up to the diameter. Cyclic shifts give n unordered
pairs at each shorter length and at least n/2 pairs at the diameter.
Summing their squared multiplicities gives the asserted lower bound.
-/

open Finset EuclideanGeometry Erdos94 Real

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private noncomputable def point (t : ℝ) : Plane := !₂[cos t, sin t]
private noncomputable def stepAngle (n : ℕ) := 2 * π / n
private noncomputable def vertex (n i : ℕ) := point (stepAngle n * i)
private noncomputable def chord (n k : ℕ) := dist (vertex n 0) (vertex n k)

private lemma point_dist (a b : ℝ) : dist (point a) (point b)^2 = 2 - 2*cos (b-a) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, cos_sub]
  simp [point, Real.dist_eq, sq_abs]
  nlinarith [sin_sq_add_cos_sq a, sin_sq_add_cos_sq b]

private lemma vertex_mem {i n : ℕ} (hi : i < n) : vertex n i ∈ regularNGon n := by
  apply Finset.mem_image.mpr
  refine ⟨i, mem_range.mpr hi, ?_⟩
  unfold vertex point stepAngle
  rw [show 2 * π / n * i = 2 * π * i / n by ring]

private lemma vertex_inj {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun i : Fin n => vertex n i.val) := by
  intro i j he
  let t := stepAngle n
  have ht : 0 < t := by unfold t stepAngle; positivity
  have htn : t*n = 2*π := div_mul_cancel₀ _ (by positivity)
  have hi : (i.val:ℝ) < n := by exact_mod_cast i.isLt
  have hj : (j.val:ℝ) < n := by exact_mod_cast j.isLt
  have hh := point_dist (t*i.val) (t*j.val)
  change point (t*i.val) = point (t*j.val) at he
  rw [he, dist_self, zero_pow (by decide)] at hh
  have H : cos (t*j.val-t*i.val) = 1 := by linarith
  have lo : -(2*π) < t*j.val-t*i.val := by
    linarith [mul_nonneg ht.le (Nat.cast_nonneg (α:=ℝ) j.val), mul_lt_mul_of_pos_left hi ht]
  have up : t*j.val-t*i.val < 2*π := by
    linarith [mul_nonneg ht.le (Nat.cast_nonneg (α:=ℝ) i.val), mul_lt_mul_of_pos_left hj ht]
  have eq0 := (cos_eq_one_iff_of_lt_of_lt lo up).1 H
  apply Fin.ext
  exact_mod_cast (mul_left_cancel₀ ht.ne' (sub_eq_zero.mp eq0).symm)

private lemma chord_sq (n k : ℕ) : chord n k ^ 2 = 2 - 2*cos (stepAngle n*k) := by
  simpa [chord, vertex] using point_dist (stepAngle n * (0:ℕ)) (stepAngle n*k)

private lemma chord_inj (n : ℕ) (hn : 0 < n) : Set.InjOn (chord n) (Set.Icc 1 (n/2)) := by
  intro a ha b hb h
  have ht : 0 < stepAngle n := by unfold stepAngle; positivity
  have htn : stepAngle n*n = 2*π := div_mul_cancel₀ _ (by positivity)
  have interval (k : ℕ) (hk : k ≤ n/2) : stepAngle n*k ∈ Set.Icc (0:ℝ) π := by
    refine ⟨by positivity, ?_⟩
    have hk' : (2:ℝ)*k ≤ n := by exact_mod_cast (show 2*k ≤ n by omega)
    nlinarith [mul_le_mul_of_nonneg_left hk' ht.le]
  have hh := congrArg (· ^ 2) h
  simp only [chord_sq] at hh
  have hc : cos (stepAngle n*a) = cos (stepAngle n*b) := by linarith
  exact_mod_cast (mul_left_cancel₀ ht.ne' (strictAntiOn_cos.injOn (interval _ ha.2) (interval _ hb.2) hc))

private lemma shift_dist {n i k : ℕ} (hi : i < n) (hk : k < n) :
    dist (vertex n i) (vertex n ((i+k)%n)) = chord n k := by
  have hn : 0 < n := by omega
  let t := stepAngle n
  have htn : t*n = 2*π := div_mul_cancel₀ _ (by positivity)
  have sqd := point_dist (t*i) (t*((i+k)%n : ℕ))
  change dist (vertex n i) (vertex n ((i+k)%n)) ^ 2 = _ at sqd
  have cosId : cos (t*((i+k)%n : ℕ)-t*i) = cos (t*k) := by
    by_cases h : i+k < n
    · rw [Nat.mod_eq_of_lt h, Nat.cast_add]; congr 1; ring
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ i+k), Nat.mod_eq_of_lt (by omega), Nat.cast_sub (by omega : n ≤ i+k), Nat.cast_add]
      rw [show t*((i:ℝ)+k-n)-t*i = t*k-2*π by linarith only [htn], cos_sub_two_pi]
  rw [cosId] at sqd
  have d := chord_sq n k
  change _ = 2-2*cos (t*k) at d
  exact (sq_eq_sq₀ dist_nonneg (show 0 ≤ chord n k from dist_nonneg)).mp (sqd.trans d.symm)

private lemma shift_ne {n i k : ℕ} (hi : i < n) (hk : k < n) (hpos : 0 < k) : (i+k)%n ≠ i := by
  by_cases h : i+k<n
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega : n ≤ i+k), Nat.mod_eq_of_lt (by omega)]; omega

private lemma chord_count (n k : ℕ) (hk : 0 < k) (hhalf : 2*k ≤ n) :
    chord n k ∈ distanceSet (regularNGon n) ∧
    n/2 ≤ distanceMultiplicity (regularNGon n) (chord n k) ∧
    (2*k < n → n ≤ distanceMultiplicity (regularNGon n) (chord n k)) := by
  classical
  have hn : 0 < n := by omega
  let P := regularNGon n
  let len := chord n k
  let X := P.offDiag.filter fun e : Plane × Plane => dist e.1 e.2 = len
  let s (i : Fin n) : Fin n := ⟨(i.val+k)%n, Nat.mod_lt _ hn⟩
  let v (i : Fin n) := vertex n i.val
  let e (i : Fin n) := (v i, v (s i))
  let f (i : Fin n) := (v (s i), v i)
  have inj : Function.Injective v := vertex_inj hn
  have en (i : Fin n) : v (s i) ≠ v i := by
    intro he
    exact shift_ne i.isLt (by omega : k < n) hk (congrArg Fin.val (inj he))
  have memE (i : Fin n) : e i ∈ X := by
    refine mem_filter.mpr ⟨mem_offDiag.mpr ⟨vertex_mem i.isLt, vertex_mem (s i).isLt, (en i).symm⟩, ?_⟩
    exact shift_dist i.isLt (by omega)
  have memF (i : Fin n) : f i ∈ X := by
    refine mem_filter.mpr ⟨mem_offDiag.mpr ⟨vertex_mem (s i).isLt, vertex_mem i.isLt, en i⟩, ?_⟩
    exact (dist_comm _ _).trans (shift_dist i.isLt (by omega))
  let E := univ.image e
  let F := univ.image f
  have ecard : E.card = n := by
    rw [Finset.card_image_of_injective _ (show Function.Injective e from fun i j h => inj (congrArg Prod.fst h))]
    exact Fintype.card_fin n
  have fcard : F.card = n := by
    rw [Finset.card_image_of_injective _ (show Function.Injective f from fun i j h => inj (congrArg Prod.snd h))]
    exact Fintype.card_fin n
  have esub : E ⊆ X := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := mem_image.mp hp
    exact memE i
  have fsub : F ⊆ X := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := mem_image.mp hp
    exact memF i
  have cardX := Finset.card_le_card esub
  rw [ecard] at cardX
  let i : Fin n := ⟨0,hn⟩
  obtain ⟨h₁,h₂⟩ := mem_filter.mp (memE i)
  refine ⟨mem_image.mpr ⟨e i,h₁,h₂⟩, ?_, ?_⟩
  · change n/2 ≤ X.card/2
    omega
  · intro hstrict
    have disj : Disjoint E F := by
      rw [Finset.disjoint_left]
      intro p hp hq
      obtain ⟨i,_,rfl⟩ := mem_image.mp hp
      obtain ⟨j,_,he⟩ := mem_image.mp hq
      have h₁ : s j = i := inj (congrArg Prod.fst he)
      have h₂ : j = s i := inj (congrArg Prod.snd he)
      have hval := congrArg Fin.val (h₂ ▸ h₁)
      change ((i.val+k)%n+k)%n = i.val at hval
      rw [Nat.mod_add_mod, Nat.add_assoc] at hval
      exact shift_ne i.isLt (by omega : k+k<n) (by omega) hval
    have cardEF := Finset.card_le_card (Finset.union_subset esub fsub)
    rw [Finset.card_union_of_disjoint disj, ecard, fcard] at cardEF
    change n ≤ X.card/2
    omega

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H1 := by
  classical
  intro n
  by_cases hzero : n = 0
  · subst n; simp
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn := Nat.pos_of_ne_zero hzero
  let S := Finset.Icc 1 (n/2)
  let M := distanceMultiplicity (regularNGon n)
  have count (k : ℕ) (hk : k ∈ S) := chord_count n k (mem_Icc.mp hk).1
    (by have := (mem_Icc.mp hk).2; omega)
  have sub : S.image (chord n) ⊆ distanceSet (regularNGon n) := by
    intro u hu
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hu
    exact (count k hk).1
  have total : ∑ k ∈ S, (M (chord n k) : ℝ)^2 ≤
      ∑ u ∈ distanceSet (regularNGon n), (M u : ℝ)^2 := by
    rw [← Finset.sum_image (f := fun u => (M u : ℝ)^2) (g := chord n)]
    · exact sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => sq_nonneg _)
    · exact fun i hi j hj hij => chord_inj n hn (mem_Icc.mp hi) (mem_Icc.mp hj) hij
  apply le_trans _ total
  have hcard : S.card = n/2 := by simp [S]
  split_ifs with odd
  · have lt (i : ℕ) (hi : i ∈ S) : 2*i < n := by have := (mem_Icc.mp hi).2; omega
    have h := Finset.sum_le_sum (s := S) (f := fun _ => (n : ℝ)^2)
      (g := fun i => (M (chord n i):ℝ)^2) (fun i hi => by
        have hh : (n : ℝ) ≤ M (chord n i) := by exact_mod_cast (count i hi).2.2 (lt i hi)
        gcongr)
    rw [sum_const, hcard, nsmul_eq_mul] at h
    have he : 2*(n/2)+1 = n := by omega
    have he' : (2 : ℝ)*((n/2 : ℕ):ℝ)+1 = n := by exact_mod_cast he
    nlinarith [congrArg (fun x : ℝ => x * (n:ℝ)^2) he']
  · let l := n/2
    have he : 2*l = n := by dsimp [l]; omega
    have he' : (2:ℝ)*l = n := by exact_mod_cast he
    have hl : l ∈ S := mem_Icc.mpr ⟨by dsimp [l] at *; omega, le_rfl⟩
    rw [← Finset.sum_erase_add _ _ hl]
    have h := Finset.sum_le_sum (s := S.erase l) (f := fun _ => (n:ℝ)^2)
      (g := fun i => (M (chord n i):ℝ)^2) (fun i hi => by
        obtain ⟨hne,hmem⟩ := mem_erase.mp hi
        have hh : 2*i < n := by have := (mem_Icc.mp hmem).2; dsimp [l] at *; omega
        have H : (n:ℝ) ≤ M (chord n i) := by exact_mod_cast (count i hmem).2.2 hh
        gcongr)
    rw [sum_const, card_erase_of_mem hl, hcard, nsmul_eq_mul] at h
    have hlpos : 1 ≤ l := (mem_Icc.mp hl).1
    have hdiam : (l:ℝ) ≤ M (chord n l) := by exact_mod_cast (count l hl).2.1
    have hdiam2 : (l:ℝ)^2 ≤ (M (chord n l):ℝ)^2 := by gcongr
    change ((l-1:ℕ):ℝ)*_ ≤ _ at h
    rw [Nat.cast_sub hlpos, Nat.cast_one] at h
    calc
      _ = ((l:ℝ)-1)*n^2+(l:ℝ)^2 := by rw [← he']; ring
      _ ≤ _ := add_le_add h hdiam2
