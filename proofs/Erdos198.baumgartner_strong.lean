import FormalConjectures.ErdosProblems.«198»

/-!
# Baumgartner's progression theorem

Use the finitely supported rational coordinates of a Hamel basis. Enumerate
the coefficient patterns of pairs and choose one point in each pattern
whose changing coordinates are much larger than all earlier radii.
Retain each radius together with the value at the first large coordinate.

For three points in a fixed-length progression, a highest layer cannot
occur exactly once or twice. If all three points lie on one radius,
strict convexity of the squared coordinate sum forces equality.

This adapts the coefficient-pattern construction in James E. Baumgartner,
*Partitioning vector spaces* (1975), to arbitrary fixed progression length.
-/

-- Credit: @ysanatomic

namespace OMA.Baumgartner198

structure Pattern where
  n : ℕ
  start : Fin n → ℚ
  step : Fin n → ℚ
  nonzero : ∃ i, step i ≠ 0

def cutoff (k : ℕ) (T : ℚ) : ℚ := (2 * ((k : ℚ) + 1)) * T

def sample (p : Pattern) (m : ℕ) (i : Fin p.n) : ℚ :=
  p.start i + (m : ℚ) * p.step i

structure Stage (k : ℕ) (p : Pattern) where
  threshold : ℚ
  time : ℕ
  first : Fin p.n
  positive : 0 < threshold
  bounded_start : ∀ i, |p.start i| ≤ threshold
  large_step : ∀ i, p.step i ≠ 0 → cutoff k threshold < |sample p time i|
  first_step : p.step first ≠ 0
  earlier_step : ∀ i < first, p.step i = 0

def radius {k : ℕ} {p : Pattern} (s : Stage k p) : ℚ :=
  ∑ i, (sample p s.time i)^2

def mark {k : ℕ} {p : Pattern} (s : Stage k p) : ℚ := sample p s.time s.first

def squaredSize {ι : Type*} (f : ι →₀ ℚ) : ℚ := f.sum (fun _ a ↦ a^2)

def InLayer {ι : Type*} [LinearOrder ι] (k : ℕ) (T R c : ℚ) (f : ι →₀ ℚ) : Prop :=
  squaredSize f = R ∧
  (∀ i, |f i| ≤ T ∨ cutoff k T < |f i|) ∧
  ∃ j, cutoff k T < |f j| ∧ f j = c ∧ ∀ i < j, |f i| ≤ T

end OMA.Baumgartner198

namespace OMA.Baumgartner198

private instance : Countable Pattern := by
  let encode (p : Pattern) : Σ n : ℕ, (Fin n → ℚ) × (Fin n → ℚ) :=
    ⟨p.n, p.start, p.step⟩
  refine Function.Injective.countable (f := encode) ?_
  rintro ⟨n, a, d, hd⟩ ⟨n', a', d', hd'⟩ h
  change (⟨n, a, d⟩ : Σ i : ℕ, (Fin i → ℚ) × (Fin i → ℚ)) = ⟨n', a', d'⟩ at h
  cases h
  rfl

private instance : Nonempty Pattern :=
  ⟨⟨1, fun _ ↦ 0, fun _ ↦ 1, ⟨0, one_ne_zero⟩⟩⟩

private theorem stage_above (k : ℕ) (p : Pattern) (B : ℚ) :
    ∃ s : Stage k p, B ≤ s.threshold := by
  classical
  let T : ℚ := max B 1 + ∑ i, |p.start i|
  have hSum : 0 ≤ ∑ i, |p.start i| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hT : 0 < T := by
    have hOne : (1 : ℚ) ≤ max B 1 := le_max_right _ _
    dsimp [T]
    linarith
  have hBound : ∀ i, |p.start i| ≤ T := by
    intro i
    have hi : |p.start i| ≤ ∑ j, |p.start j| :=
      Finset.single_le_sum (f := fun j ↦ |p.start j|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
    exact hi.trans (le_add_of_nonneg_left ((zero_le_one : (0 : ℚ) ≤ 1).trans (le_max_right _ _)))
  have hCut : 0 ≤ cutoff k T := by
    unfold cutoff
    positivity
  let bound (i : Fin p.n) : ℚ := (cutoff k T + |p.start i|) / |p.step i|
  have hBoundNonneg (i : Fin p.n) : 0 ≤ bound i :=
    div_nonneg (add_nonneg hCut (abs_nonneg _)) (abs_nonneg _)
  obtain ⟨m, hm⟩ := exists_nat_gt (∑ i, bound i)
  let support := Finset.univ.filter (fun i : Fin p.n ↦ p.step i ≠ 0)
  have hs : support.Nonempty := by
    obtain ⟨i, hi⟩ := p.nonzero
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨⟨T, m, support.min' hs, hT, hBound, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    have hb : bound i < (m : ℚ) :=
      (Finset.single_le_sum (f := bound) (fun j _ ↦ hBoundNonneg j)
        (Finset.mem_univ i)).trans_lt hm
    have hmStep : cutoff k T + |p.start i| < (m : ℚ) * |p.step i| :=
      (div_lt_iff₀ (abs_pos.mpr hi)).mp hb
    have hTriangle := abs_sub (sample p m i) (p.start i)
    rw [show sample p m i - p.start i = (m : ℚ) * p.step i by
      unfold sample
      ring, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hTriangle
    linarith
  · exact (Finset.mem_filter.mp (Finset.min'_mem support hs)).2
  · intro i hi
    by_contra hn
    exact (not_lt_of_ge (Finset.min'_le support i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))) hi
  · exact (le_max_left B 1).trans (le_add_of_nonneg_right hSum)

theorem exists_growing_stages (k : ℕ) :
    ∃ e : ℕ → Pattern, Function.Surjective e ∧
      ∃ s : ∀ n, Stage k (e n), ∀ m n, m < n → radius (s m) + 1 ≤ (s n).threshold := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat Pattern
  let chooseStage (n : ℕ) (B : ℚ) : Stage k (e n) := (stage_above k (e n) B).choose
  have hChoose (n : ℕ) (B : ℚ) : B ≤ (chooseStage n B).threshold :=
    (stage_above k (e n) B).choose_spec
  let B : ℕ → ℚ := Nat.rec 0 (fun n b ↦ max b (radius (chooseStage n b) + 1))
  have hB (n : ℕ) : B (n + 1) = max (B n) (radius (chooseStage n (B n)) + 1) := rfl
  have hMono : Monotone B := monotone_nat_of_le_succ fun n ↦
    (le_max_left _ _).trans_eq (hB n).symm
  let s (n : ℕ) : Stage k (e n) := chooseStage n (B n)
  refine ⟨e, he, s, fun m n hmn ↦ ?_⟩
  calc
    radius (s m) + 1 ≤ B (m + 1) := (le_max_right _ _).trans_eq (hB m).symm
    _ ≤ B n := hMono hmn
    _ ≤ (s n).threshold := hChoose n (B n)

end OMA.Baumgartner198

namespace OMA.Baumgartner198

/-- Enumerating the joint support in increasing order realizes the same coefficient pattern. -/
lemma capture_progression {ι : Type*} [LinearOrder ι] {k : ℕ}
    (e : ℕ → Pattern) (he : Function.Surjective e) (s : ∀ n, Stage k (e n))
    (x y : ι →₀ ℚ) (hy : y ≠ 0) :
    ∃ n m : ℕ, InLayer k (s n).threshold (radius (s n)) (mark (s n)) (x + m • y) := by
  let U := x.support ∪ y.support
  let q := U.orderIsoOfFin rfl
  let p : Pattern := {
    n := U.card
    start := fun i => x (q i).val
    step := fun i => y (q i).val
    nonzero := by
      obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hy
      let jU : ↥U := ⟨j, Finset.mem_union_right _ hj⟩
      refine ⟨q.symm jU, ?_⟩
      simpa [jU] using Finsupp.mem_support_iff.mp hj
  }
  have realize (p' : Pattern) (hp : p' = p) (st : Stage k p') :
      InLayer k st.threshold (radius st) (mark st) (x + st.time • y) := by
    subst p'
    let f := x + st.time • y
    have hoff (j : ι) (hj : j ∉ U) : f j = 0 := by
      have hzero : x j = 0 ∧ y j = 0 := by
        simpa [U, Finsupp.mem_support_iff, not_or] using hj
      simp [f, Finsupp.add_apply, Finsupp.smul_apply, hzero]
    have hcoeff (i : Fin p.n) : f (q i).val = sample p st.time i := by
      simp [f, p, sample, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
    have hsmall (i : Fin p.n) (hi : p.step i = 0) : |f (q i).val| ≤ st.threshold := by
      rw [hcoeff, sample, hi, mul_zero, add_zero]
      exact st.bounded_start i
    have hlarge (i : Fin p.n) (hi : p.step i ≠ 0) :
        cutoff k st.threshold < |f (q i).val| := by
      rw [hcoeff]
      exact st.large_step i hi
    have hsupp : f.support ⊆ U := fun j hj => by
      by_contra hout
      exact (Finsupp.mem_support_iff.mp hj) (hoff j hout)
    refine ⟨?_, ?_, (q st.first).val, hlarge _ st.first_step, hcoeff _, ?_⟩
    · rw [squaredSize, Finsupp.sum_of_support_subset f hsupp _ (fun _ _ => by simp), radius]
      symm
      refine Finset.sum_bij (fun i _ => (q i).val) (fun i _ => (q i).property) ?_ ?_ ?_
      · intro i _ j _ hij
        exact q.injective (Subtype.ext hij)
      · intro j hj
        refine ⟨q.symm ⟨j, hj⟩, Finset.mem_univ _, ?_⟩
        simp
      · intro i _
        rw [hcoeff]
    · intro j
      by_cases hj : j ∈ U
      · let i := q.symm ⟨j, hj⟩
        have hi : (q i).val = j := by simp [i]
        rw [← hi]
        by_cases hz : p.step i = 0
        · exact Or.inl (hsmall i hz)
        · exact Or.inr (hlarge i hz)
      · rw [hoff j hj, abs_zero]
        exact Or.inl st.positive.le
    · intro j hj
      by_cases hjU : j ∈ U
      · let i := q.symm ⟨j, hjU⟩
        have hi : (q i).val = j := by simp [i]
        have hlt : q i < q st.first := by
          change (q i).val < (q st.first).val
          rwa [hi]
        change |f j| ≤ st.threshold
        rw [← hi]
        exact hsmall i (st.earlier_step i (q.lt_iff_lt.mp hlt))
      · rw [hoff j hjU, abs_zero]
        exact st.positive.le
  obtain ⟨n, hn⟩ := he p
  exact ⟨n, (s n).time, realize (e n) hn (s n)⟩

end OMA.Baumgartner198

namespace OMA.Baumgartner198

private lemma one_large_coordinate (k : ℕ) {T x y z a b c : ℚ} (hT : 0 < T)
    (hx : cutoff k T < |x|) (hy : |y| ≤ T) (hz : |z| ≤ T)
    (ha : 1 ≤ |a|) (hb : |b| ≤ k) (hc : |c| ≤ k)
    (hrel : a * x + b * y + c * z = 0) : False := by
  have hax : |x| ≤ |a * x| := by
    rw [abs_mul, ← one_mul |x|]
    simpa using mul_le_mul_of_nonneg_right ha (abs_nonneg x)
  have hby : |b * y| ≤ (k : ℚ) * T := by
    rw [abs_mul]
    exact mul_le_mul hb hy (abs_nonneg _) (Nat.cast_nonneg _)
  have hcz : |c * z| ≤ (k : ℚ) * T := by
    rw [abs_mul]
    exact mul_le_mul hc hz (abs_nonneg _) (Nat.cast_nonneg _)
  have hadd : |a * x| ≤ |b * y| + |c * z| := by
    rw [show a * x = -(b * y + c * z) by linarith, abs_neg]
    exact abs_add_le _ _
  unfold cutoff at hx
  linarith

private lemma ordered_layer_conflict {ι : Type*} [LinearOrder ι] (k : ℕ)
    (T R M : ℕ → ℚ) (hT : ∀ n, 0 < T n)
    (hprev : ∀ m n, m < n → ∀ f : ι →₀ ℚ,
      InLayer k (T m) (R m) (M m) f → ∀ i, |f i| ≤ T n)
    {x y z : ι →₀ ℚ} {nx ny nz : ℕ}
    (hx : InLayer k (T nx) (R nx) (M nx) x)
    (hy : InLayer k (T ny) (R ny) (M ny) y)
    (hz : InLayer k (T nz) (R nz) (M nz) z)
    {a b c : ℚ} (habc : a + b + c = 0)
    (ha : 1 ≤ |a| ∧ |a| ≤ k) (hb : 1 ≤ |b| ∧ |b| ≤ k)
    (hc : 1 ≤ |c| ∧ |c| ≤ k)
    (hrel : ∀ i, a * x i + b * y i + c * z i = 0)
    (hyz : ny ≤ nz) (hxz : nx < nz) : False := by
  obtain ⟨jz, hzhi, hzmark, hzearly⟩ := hz.2.2
  rcases lt_or_eq_of_le hyz with hyz | rfl
  · exact one_large_coordinate k (hT nz) hzhi (hprev nx nz hxz x hx jz)
      (hprev ny nz hyz y hy jz) hc.1 ha.2 hb.2 (by linarith [hrel jz])
  obtain ⟨jy, hyhi, hymark, hyearly⟩ := hy.2.2
  rcases lt_trichotomy jy jz with hj | rfl | hj
  · exact one_large_coordinate k (hT ny) hyhi (hprev nx ny hxz x hx jy)
      (hzearly jy hj) hb.1 ha.2 hc.2 (by linarith [hrel jy])
  · have ha0 : a ≠ 0 := by
      intro h
      have hlo := ha.1
      norm_num [h] at hlo
    have hprod : a * (x jy - M ny) = 0 := by
      have h := hrel jy
      rw [hymark, hzmark] at h
      linear_combination h - M ny * habc
    have hmark : x jy = M ny :=
      sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha0)
    have hxlow := hprev nx ny hxz x hx jy
    rw [hmark] at hxlow
    rw [hymark] at hyhi
    have hcut : T ny ≤ cutoff k (T ny) := by
      unfold cutoff
      have hmul : 0 ≤ (k : ℚ) * T ny := mul_nonneg (Nat.cast_nonneg _) (hT ny).le
      linarith [hT ny]
    exact (not_lt_of_ge (hxlow.trans hcut)) hyhi
  · exact one_large_coordinate k (hT ny) hzhi (hprev nx ny hxz x hx jz)
      (hyearly jz hj) hc.1 ha.2 hb.2 (by linarith [hrel jz])

lemma distinct_layer_conflict {ι : Type*} [LinearOrder ι] (k : ℕ)
    (T R M : ℕ → ℚ) (hT : ∀ n, 0 < T n)
    (hprev : ∀ m n, m < n → ∀ f : ι →₀ ℚ,
      InLayer k (T m) (R m) (M m) f → ∀ i, |f i| ≤ T n)
    {x y z : ι →₀ ℚ} {nx ny nz : ℕ}
    (hx : InLayer k (T nx) (R nx) (M nx) x)
    (hy : InLayer k (T ny) (R ny) (M ny) y)
    (hz : InLayer k (T nz) (R nz) (M nz) z)
    {a b c : ℚ} (habc : a + b + c = 0)
    (ha : 1 ≤ |a| ∧ |a| ≤ k) (hb : 1 ≤ |b| ∧ |b| ≤ k)
    (hc : 1 ≤ |c| ∧ |c| ≤ k)
    (hrel : ∀ i, a * x i + b * y i + c * z i = 0)
    (hdiff : ¬ (nx = ny ∧ ny = nz)) : False := by
  rcases le_total nx ny with hxy | hyx
  · rcases le_total ny nz with hyz | hzy
    · exact ordered_layer_conflict k T R M hT hprev hx hy hz habc ha hb hc hrel hyz (by omega)
    · rcases le_total nx nz with hxz | hzx
      · exact ordered_layer_conflict k T R M hT hprev hx hz hy
          (by linarith) ha hc hb (fun i ↦ by linarith [hrel i]) hzy (by omega)
      · exact ordered_layer_conflict k T R M hT hprev hz hx hy
          (by linarith) hc ha hb (fun i ↦ by linarith [hrel i]) hxy (by omega)
  · rcases le_total nx nz with hxz | hzx
    · exact ordered_layer_conflict k T R M hT hprev hy hx hz
        (by linarith) hb ha hc (fun i ↦ by linarith [hrel i]) hxz (by omega)
    · rcases le_total ny nz with hyz | hzy
      · exact ordered_layer_conflict k T R M hT hprev hy hz hx
          (by linarith) hb hc ha (fun i ↦ by linarith [hrel i]) hzx (by omega)
      · exact ordered_layer_conflict k T R M hT hprev hz hy hx
          (by linarith) hc hb ha (fun i ↦ by linarith [hrel i]) hyx (by omega)

end OMA.Baumgartner198

namespace OMA.Baumgartner198

open Finset

private theorem coordinate_le_squaredSize_add_one {ι : Type*} (f : ι →₀ ℚ) (i : ι) :
    |f i| ≤ squaredSize f + 1 := by
  classical
  have hs : 0 ≤ squaredSize f := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  by_cases hn : f i = 0
  · simp [hn]; linarith
  · have hi := Finsupp.mem_support_iff.mpr hn
    have hsq : (f i)^2 ≤ squaredSize f :=
      Finset.single_le_sum (f := fun j ↦ (f j)^2) (fun j _ ↦ sq_nonneg _) hi
    nlinarith [sq_nonneg (|f i| - 1/2), sq_abs (f i)]

private theorem same_radius_endpoints {ι : Type*} (x y z : ι →₀ ℚ) {a b : ℚ}
    (ha : 0 < a) (hb : 0 < b)
    (hxy : squaredSize x = squaredSize y) (hxz : squaredSize x = squaredSize z)
    (hrel : ∀ i, a*x i + b*y i = (a+b)*z i) :
    x = y := by
  classical
  let U := (x.support ∪ y.support) ∪ z.support
  have hxU : x.support ⊆ U := fun i h ↦ mem_union_left _ (mem_union_left _ h)
  have hyU : y.support ⊆ U := fun i h ↦ mem_union_left _ (mem_union_right _ h)
  have hzU : z.support ⊆ U := fun i h ↦ mem_union_right _ h
  have he (f : ι →₀ ℚ) (hf : f.support ⊆ U) :
      squaredSize f = ∑ i ∈ U, (f i)^2 := by
    apply Finset.sum_subset hf
    intro i _ hi
    have hz : f i = 0 := Finsupp.notMem_support_iff.mp hi
    simp [hz]
  have hidentity (i : ι) :
      a*b*(x i-y i)^2 = (a+b)*(a*(x i)^2+b*(y i)^2) - (a+b)^2*(z i)^2 := by
    linear_combination -(congrArg (fun t : ℚ ↦ t^2) (hrel i))
  have hsum : a*b*(∑ i ∈ U, (x i-y i)^2) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [hidentity]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← he x hxU, ← he y hyU, ← he z hzU, ← hxy, ← hxz]
    ring
  have hs : (∑ i ∈ U, (x i-y i)^2) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left (mul_pos ha hb).ne'
  ext i
  by_cases hi : i ∈ U
  · have hle := Finset.single_le_sum (f := fun j ↦ (x j-y j)^2)
      (fun j _ ↦ sq_nonneg _) hi
    rw [hs] at hle
    nlinarith [sq_nonneg (x i-y i)]
  · rw [Finsupp.notMem_support_iff.mp (fun h ↦ hi (hxU h)),
      Finsupp.notMem_support_iff.mp (fun h ↦ hi (hyU h))]

end OMA.Baumgartner198

namespace OMA.Baumgartner198

private theorem ordered_layer_triple {ι : Type*} [LinearOrder ι] (k : ℕ) (T R C : ℕ → ℚ)
    (hT : ∀ n, 0 < T n) (hprev : ∀ m n, m < n → R m + 1 ≤ T n)
    (x d : ι →₀ ℚ) {i j l : ℕ} (hij : i < j) (hjl : j < l) (hl : l < k)
    {ni nj nl : ℕ}
    (hi : InLayer k (T ni) (R ni) (C ni) (x + i • d))
    (hj : InLayer k (T nj) (R nj) (C nj) (x + j • d))
    (hk : InLayer k (T nl) (R nl) (C nl) (x + l • d)) :
    x + i • d = x + l • d := by
  let a : ℚ := (l : ℚ) - (j : ℚ)
  let b : ℚ := (j : ℚ) - (i : ℚ)
  let c : ℚ := a+b
  have hab : 1 ≤ a ∧ 1 ≤ b := by
    have hi' : (i : ℚ)+1 ≤ (j : ℚ) := by exact_mod_cast Nat.succ_le_of_lt hij
    have hj' : (j : ℚ)+1 ≤ (l : ℚ) := by exact_mod_cast Nat.succ_le_of_lt hjl
    dsimp [a, b]
    exact ⟨by linarith, by linarith⟩
  have hc : c ≤ k := by
    have hl' : (l:ℚ) ≤ (k:ℚ) := by exact_mod_cast hl.le
    dsimp [c, a, b]
    linarith [Nat.cast_nonneg (α := ℚ) i]
  have hpa : 0 < a := lt_of_lt_of_le zero_lt_one hab.1
  have hpb : 0 < b := lt_of_lt_of_le zero_lt_one hab.2
  have hpc : 0 < c := add_pos hpa hpb
  have hrel (u : ι) : a * (x+i•d) u + b * (x+l•d) u = c * (x+j•d) u := by
    simp only [Finsupp.add_apply, Finsupp.nsmul_apply, nsmul_eq_mul]
    dsimp [a, b, c]
    ring
  by_cases heq : ni = nl ∧ nl = nj
  · exact same_radius_endpoints _ _ _ hpa hpb
      (by rw [hi.1, hk.1, heq.1]) (by rw [hi.1, hj.1, heq.1, heq.2]) hrel
  · exfalso
    have hpast (m n : ℕ) (hmn : m < n) (f : ι →₀ ℚ)
        (hf : InLayer k (T m) (R m) (C m) f) (u : ι) : |f u| ≤ T n := by
      have hx := coordinate_le_squaredSize_add_one f u
      rw [hf.1] at hx
      exact hx.trans (hprev m n hmn)
    have ha : 1 ≤ |a| ∧ |a| ≤ (k:ℚ) := by
      rw [abs_of_pos hpa]
      exact ⟨hab.1, by dsimp [c] at hc; linarith⟩
    have hb : 1 ≤ |b| ∧ |b| ≤ (k:ℚ) := by
      rw [abs_of_pos hpb]
      exact ⟨hab.2, by dsimp [c] at hc; linarith⟩
    have hcn : 1 ≤ |-c| ∧ |-c| ≤ (k:ℚ) := by
      rw [abs_neg, abs_of_pos hpc]
      refine ⟨?_, hc⟩
      dsimp [c]
      linarith [hab.1, hab.2]
    exact distinct_layer_conflict k T R C hT hpast hi hk hj
      (a := a) (b := b) (c := -c) (by dsimp [c]; ring) ha hb hcn
      (fun u ↦ by linarith [hrel u]) heq

end OMA.Baumgartner198

open OMA.Baumgartner198 in
theorem OMA.solution : type_of% @Erdos198.baumgartner_strong := by
  classical
  intro V _ _ k
  let ι := Module.Basis.ofVectorSpaceIndex ℚ V
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  let eV : V ≃ₗ[ℚ] (ι →₀ ℚ) := (Module.Basis.ofVectorSpace ℚ V).repr
  obtain ⟨e, he, s, hs⟩ := exists_growing_stages k
  let T (n : ℕ) := (s n).threshold
  let R (n : ℕ) := radius (s n)
  let C (n : ℕ) := mark (s n)
  let X : Set V := {x | ∃ n, InLayer k (T n) (R n) (C n) (eV x)}
  refine ⟨X, ?_, ?_⟩
  · intro Y hY
    obtain ⟨a, d, hY⟩ := hY
    have hd : d ≠ 0 := by
      intro h
      have hy : Y = {a} := by
        rw [hY.eq, h]
        ext b
        constructor
        · rintro ⟨m, _, rfl⟩
          simp
        · intro hb
          obtain rfl := Set.mem_singleton_iff.mp hb
          exact ⟨0, by simp, by simp⟩
      have hy' := hY.card
      change Y.encard = ⊤ at hy'
      simp [hy] at hy'
    have hd' : eV d ≠ 0 := fun h ↦ hd (eV.injective (h.trans eV.map_zero.symm))
    obtain ⟨n, m, hm⟩ := capture_progression e he s (eV a) (eV d) hd'
    refine ⟨a + m • d, ⟨n, ?_⟩, ?_⟩
    · simpa only [map_add, map_nsmul] using hm
    · rw [hY.eq]
      exact ⟨m, by simp, rfl⟩
  · intro Y hY
    obtain ⟨a, d, hY⟩ := hY
    have hFin : Y.Finite := Set.finite_of_encard_eq_coe hY.card
    by_contra! hbad
    obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ :=
      (Set.two_lt_ncard_iff (hFin.subset Set.inter_subset_right)).mp hbad
    let f (n : ℕ) := a + n • d
    have hn (x : V) (hx : x ∈ Y) : ∃ i : ℕ, i < k ∧ x = f i := by
      rw [hY.eq] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact ⟨i, ENat.coe_lt_coe.mp hi, rfl⟩
    have horder (i j l : ℕ) (hij : i < j) (hjl : j < l) (hl : l < k)
        (hiX : f i ∈ X) (hjX : f j ∈ X) (hlX : f l ∈ X) :
        f i = f l := by
      obtain ⟨ni, hni⟩ := hiX
      obtain ⟨nj, hnj⟩ := hjX
      obtain ⟨nl, hnl⟩ := hlX
      apply eV.injective
      simp only [f, map_add, map_nsmul] at hni hnj hnl ⊢
      exact ordered_layer_triple k T R C (fun n ↦ (s n).positive) hs
        (eV a) (eV d) hij hjl hl hni hnj hnl
    obtain ⟨i, hi, rfl⟩ := hn u hu.2
    obtain ⟨j, hj, rfl⟩ := hn v hv.2
    obtain ⟨l, hl, rfl⟩ := hn w hw.2
    have hij : i ≠ j := fun h ↦ huv (congrArg f h)
    have hil : i ≠ l := fun h ↦ huw (congrArg f h)
    have hjl : j ≠ l := fun h ↦ hvw (congrArg f h)
    rcases lt_or_gt_of_ne hij with h₁ | h₁
    · rcases lt_or_gt_of_ne hjl with h₂ | h₂
      · exact huw (horder i j l h₁ h₂ hl hu.1 hv.1 hw.1)
      · rcases lt_or_gt_of_ne hil with h₃ | h₃
        · exact huv (horder i l j h₃ h₂ hj hu.1 hw.1 hv.1)
        · exact hvw (horder l i j h₃ h₁ hj hw.1 hu.1 hv.1).symm
    · rcases lt_or_gt_of_ne hil with h₂ | h₂
      · exact hvw (horder j i l h₁ h₂ hl hv.1 hu.1 hw.1)
      · rcases lt_or_gt_of_ne hjl with h₃ | h₃
        · exact huv (horder j l i h₃ h₂ hi hv.1 hw.1 hu.1).symm
        · exact huw (horder l j i h₃ h₁ hi hw.1 hv.1 hu.1).symm
