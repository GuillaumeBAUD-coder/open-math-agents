import FormalConjectures.ErdosProblems.«193»
import Mathlib.Order.KonigLemma
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# The planar case of Erdős Problem 193

Extract an injective ray, then use the eventual signs of integer projections
to obtain a limiting direction. Dirichlet approximation yields a projection
with too few levels to hold the vertices of the ray.

The planar theorem is due to Gerver and Ramsey, *On certain sequences of
lattice points* (1979).
-/

-- Credit: @ysanatomic

open Filter
open scoped Topology

private def SparseProjection (f : ℕ → ℤ) : Prop :=
  ∀ i j k, f i = f j → f j = f k → i = j ∨ j = k ∨ i = k

private theorem count_in_interval {f : ℕ → ℤ} (hf : SparseProjection f)
    {s : Finset ℕ} {l u : ℤ} (hs : ∀ i ∈ s, f i ∈ Finset.Icc l u) :
    s.card ≤ 2 * (Finset.Icc l u).card := by
  have hcard (b : ℤ) : (s.filter fun i ↦ f i = b).card ≤ 2 := by
    by_contra! h
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp h
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    rcases hf i j k (hi'.trans hj'.symm) (hj'.trans hk'.symm) with h | h | h
    · exact hij h
    · exact hjk h
    · exact hik h
  calc
    s.card = ∑ b ∈ Finset.Icc l u, (s.filter fun i ↦ f i = b).card :=
      Finset.card_eq_sum_card_fiberwise hs
    _ ≤ ∑ _b ∈ Finset.Icc l u, 2 := Finset.sum_le_sum fun b _ ↦ hcard b
    _ = _ := by simp [mul_comm]

private theorem eventually_projection_sign {f : ℕ → ℤ} (hf : SparseProjection f)
    {L : ℤ} (hL : 0 ≤ L) (hstep : ∀ n, |f (n + 1) - f n| ≤ L) :
    (∀ᶠ n in atTop, 0 < f n) ∨ (∀ᶠ n in atTop, f n < 0) := by
  let s : Set ℕ := {n | f n ∈ Finset.Icc (-L) L}
  have hfin : s.Finite := by
    by_contra h
    obtain ⟨t, hts, ht⟩ := (Set.not_finite.mp h).exists_subset_card_eq
      (2 * (Finset.Icc (-L) L).card + 1)
    have hle := count_in_interval hf (s := t) (l := -L) (u := L)
      (fun i hi ↦ hts hi)
    omega
  obtain ⟨T, hT⟩ := hfin.bddAbove
  have hout (n : ℕ) (hn : T + 1 ≤ n) : f n < -L ∨ L < f n := by
    have hm : n ∉ s := by
      intro hm
      have : n ≤ T := hT hm
      omega
    change f n ∉ Finset.Icc (-L) L at hm
    rw [Finset.mem_Icc] at hm
    omega
  rcases hout (T + 1) le_rfl with hneg | hpos
  · right
    refine eventually_atTop.mpr ⟨T + 1, fun n hn ↦ ?_⟩
    suffices f n < -L by omega
    induction n, hn using Nat.le_induction with
    | base => exact hneg
    | succ n hn ih =>
      rcases hout (n+1) (by omega) with hn' | hn'
      · exact hn'
      · have hs := (abs_le.mp (hstep n)).2
        omega
  · left
    refine eventually_atTop.mpr ⟨T + 1, fun n hn ↦ ?_⟩
    suffices L < f n by omega
    induction n, hn using Nat.le_induction with
    | base => exact hpos
    | succ n hn ih =>
      rcases hout (n+1) (by omega) with hn' | hn'
      · have hs := (abs_le.mp (hstep n)).1
        omega
      · exact hn'

private theorem slow_projection_impossible {f : ℕ → ℤ} (hf : SparseProjection f)
    (hslow : ∀ᶠ n in atTop, |(f n : ℝ)| ≤ ((n : ℝ) + 1) / 8) : False := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hslow
  let k : ℕ := T + 1
  have hbound : (Finset.Ico T (8*k)).card ≤ 2 * (Finset.Icc (-(k : ℤ)) (k : ℤ)).card := by
    apply count_in_interval hf
    intro n hn
    obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hn
    have hle : (n : ℝ) + 1 ≤ 8*k := by exact_mod_cast (show n+1 ≤ 8*k by omega)
    have ha : |(f n : ℝ)| ≤ (k : ℝ) := by linarith [hT n hl]
    have hb : |f n| ≤ (k : ℤ) := by exact_mod_cast ha
    exact Finset.mem_Icc.mpr (abs_le.mp hb)
  rw [Nat.card_Ico, Int.card_Icc] at hbound
  dsimp [k] at *
  omega

private theorem coordinate_growth (b : ℕ → Fin 2 → ℤ) {M : ℤ}
    (hstep : ∀ n i, |b (n+1) i - b n i| ≤ M) (h0 : ∀ i, |b 0 i| ≤ M) :
    ∀ n i, |b n i| ≤ M * (n+1 : ℤ) := by
  intro n i
  induction n with
  | zero => simpa using h0 i
  | succ n ih =>
    have he : b (n+1) i = (b (n+1) i - b n i) + b n i := by ring
    calc
      |b (n+1) i| ≤ |b (n+1) i - b n i| + |b n i| := by
        nth_rw 1 [he]
        exact abs_add_le _ _
      _ ≤ M + M * (n+1 : ℤ) := add_le_add (hstep n i) ih
      _ = _ := by push_cast; ring

private theorem projection_step (b : ℕ → Fin 2 → ℤ) {M : ℤ}
    (hstep : ∀ n i, |b (n+1) i - b n i| ≤ M) (p q : ℤ) :
    ∀ n, |(p * b (n+1) 0 + q * b (n+1) 1) - (p * b n 0 + q * b n 1)| ≤
      (|p| + |q|) * M := by
  intro n
  rw [show (p * b (n+1) 0 + q * b (n+1) 1) - (p * b n 0 + q * b n 1) =
    p * (b (n+1) 0 - b n 0) + q * (b (n+1) 1 - b n 1) by ring, add_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hstep n 0) (abs_nonneg p)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hstep n 1) (abs_nonneg q)

namespace OMA.Erdos193

open Set SimpleGraph

def rayBox (x : Fin 2 → ℤ) (R : ℤ) : Set (Fin 2 → ℤ) :=
  {y | ∀ i, |y i - x i| ≤ R}

lemma rayBox_finite (x : Fin 2 → ℤ) (R : ℤ) : (rayBox x R).Finite := by
  have h : {y : Fin 2 → ℤ | ∀ i, y i ∈ Set.Icc (x i - R) (x i + R)}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  refine h.subset ?_
  intro y hy i
  obtain ⟨hlo, hhi⟩ := abs_le.mp (hy i)
  exact ⟨by omega, by omega⟩

structure RayPrefix (U : Set (Fin 2 → ℤ)) (x : U) (M : ℤ) (n : ℕ) where
  point : Fin (n + 1) → U
  start : point 0 = x
  inj : Function.Injective point
  step : ∀ j : Fin n, ∀ i, |(point j.succ).val i - (point j.castSucc).val i| ≤ M
  bound : ∀ j i, |(point j).val i - x.val i| ≤ (j.val : ℤ) * M

lemma rayPrefix_ext {U : Set (Fin 2 → ℤ)} {x : U} {M : ℤ} {n : ℕ}
    {p q : RayPrefix U x M n} (h : p.point = q.point) : p = q := by
  cases p
  cases q
  cases h
  rfl

def restrictRayPrefix {U : Set (Fin 2 → ℤ)} {x : U} {M : ℤ} {m n : ℕ}
    (h : m ≤ n) (p : RayPrefix U x M n) : RayPrefix U x M m where
  point j := p.point (Fin.castLE (Nat.succ_le_succ h) j)
  start := p.start
  inj := p.inj.comp (Fin.castLE_injective _)
  step j := p.step (Fin.castLE h j)
  bound j := p.bound (Fin.castLE (Nat.succ_le_succ h) j)

lemma rayPrefix_finite {U : Set (Fin 2 → ℤ)} {x : U} {M : ℤ} (hM : 0 ≤ M)
    (n : ℕ) : Finite (RayPrefix U x M n) := by
  let D := rayBox x.val ((n : ℤ) * M)
  let _ : Finite D := (rayBox_finite x.val _).to_subtype
  let f (p : RayPrefix U x M n) (j : Fin (n + 1)) : D :=
    ⟨(p.point j).val, fun i =>
      (p.bound j i).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt_succ j.isLt)) hM)⟩
  refine Finite.of_injective f ?_
  intro p q hpq
  apply rayPrefix_ext
  funext j
  exact Subtype.ext (congrArg (fun z : D => z.val) (congrFun hpq j))

lemma bounded_step_injective_ray (a : ℕ → Fin 2 → ℤ) (ha : (Set.range a).Infinite)
    (M : ℤ) (hM : 0 ≤ M) (hStep : ∀ n i, |a (n + 1) i - a n i| ≤ M) :
    ∃ b : ℕ → Fin 2 → ℤ, Function.Injective b ∧ Set.range b ⊆ Set.range a ∧
      ∀ n i, |b (n + 1) i - b n i| ≤ M := by
  classical
  let U := Set.range a
  let lift (n : ℕ) : U := ⟨a n, Set.mem_range_self n⟩
  let start := lift 0
  let G : SimpleGraph U :=
    { Adj := fun u v => u ≠ v ∧ ∀ i, |v.val i - u.val i| ≤ M
      symm := ⟨fun u v h => ⟨h.1.symm, fun i => by rw [abs_sub_comm]; exact h.2 i⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  have walk (n : ℕ) : Nonempty (G.Walk start (lift n)) := by
    induction n with
    | zero => exact ⟨SimpleGraph.Walk.nil⟩
    | succ n ih =>
      obtain ⟨p⟩ := ih
      by_cases h : lift n = lift (n + 1)
      · exact ⟨h ▸ p⟩
      · exact ⟨p.append (SimpleGraph.Adj.toWalk (show G.Adj (lift n) (lift (n + 1)) from ⟨h, hStep n⟩))⟩
  have wBound {u v : U} (p : G.Walk u v) (i : Fin 2) :
      |v.val i - u.val i| ≤ (p.length : ℤ) * M := by
    induction p with
    | nil => simp
    | @cons u v w huv q ih =>
      have h := (show ∀ i, |v.val i - u.val i| ≤ M from huv.2) i
      rw [SimpleGraph.Walk.length_cons, Nat.cast_add]
      calc
        |w.val i - u.val i| = |(w.val i - v.val i) + (v.val i - u.val i)| := by
          rw [sub_add_sub_cancel]
        _ ≤ |w.val i - v.val i| + |v.val i - u.val i| := abs_add_le _ _
        _ ≤ ((q.length : ℤ) + 1) * M := by linarith
  have hNonempty (n : ℕ) : Nonempty (RayPrefix U start M n) := by
    have hOut : ∃ j : ℕ, a j ∉ rayBox (a 0) ((n : ℤ) * M) := by
      by_contra! h
      exact ha ((rayBox_finite _ _).subset (Set.range_subset_iff.mpr h))
    obtain ⟨j, hj⟩ := hOut
    obtain ⟨p⟩ := walk j
    let q := p.bypass
    have hq : q.IsPath := p.bypass_isPath
    have hnq : n ≤ q.length := by
      by_contra! h
      apply hj
      intro i
      exact (wBound q i).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast h.le) hM)
    refine ⟨⟨fun l => q.getVert l.val, q.getVert_zero, ?_, ?_, ?_⟩⟩
    · intro l r h
      apply Fin.ext
      exact hq.getVert_injOn (by exact (Nat.le_of_lt_succ l.isLt).trans hnq)
        (by exact (Nat.le_of_lt_succ r.isLt).trans hnq) h
    · intro l i
      have h := q.adj_getVert_succ (l.isLt.trans_le hnq)
      exact h.2 i
    · intro l i
      exact (wBound (q.take l.val) i).trans
        (mul_le_mul_of_nonneg_right (by
          rw [SimpleGraph.Walk.take_length]
          exact_mod_cast inf_le_left) hM)
  let _ : ∀ n, Nonempty (RayPrefix U start M n) := hNonempty
  let _ : ∀ n, Finite (RayPrefix U start M n) := rayPrefix_finite hM
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => RayPrefix U start M n)
    (fun hij p => restrictRayPrefix hij p)
    (fun _ p => rayPrefix_ext (by funext j; rfl))
    (fun _ _ _ _ _ p => rayPrefix_ext (by funext j; rfl))
    (fun _ _ => Set.toFinite _)
  let b (n : ℕ) : U := (f n).point (Fin.last n)
  have hb (m n : ℕ) (h : m ≤ n) :
      (f n).point ⟨m, by omega⟩ = b m :=
    congrArg (fun p : RayPrefix U start M m => p.point (Fin.last m)) (hf h)
  refine ⟨fun n => (b n).val, ?_, ?_, ?_⟩
  · intro m n h
    have h' : b m = b n := Subtype.ext h
    let t := max m n
    have hm : m ≤ t := le_max_left _ _
    have hn : n ≤ t := le_max_right _ _
    have hpt := (f t).inj ((hb m t hm).trans (h'.trans (hb n t hn).symm))
    exact congrArg Fin.val hpt
  · rintro _ ⟨n, rfl⟩
    exact (b n).property
  · intro n i
    have h := (f (n + 1)).step (Fin.last n) i
    change |((f (n + 1)).point ⟨n + 1, by omega⟩).val i -
      ((f (n + 1)).point ⟨n, by omega⟩).val i| ≤ M at h
    rw [hb (n + 1) (n + 1) le_rfl, hb n (n + 1) (Nat.le_succ n)] at h
    exact h

end OMA.Erdos193

namespace OMA.ER193

open Filter
open scoped Topology

private theorem fixed_sign (z : ℕ → ℤ)
    (h : (∀ᶠ n in atTop, 0 < z n) ∨ (∀ᶠ n in atTop, z n < 0)) :
    ∃ s : ℤ, s ≠ 0 ∧
      ∀ᶠ n in atTop, 0 < |(z n : ℝ)| ∧ (s : ℝ) * z n = |(z n : ℝ)| := by
  rcases h with h | h
  · refine ⟨1, by decide, ?_⟩
    filter_upwards [h] with n hn
    have hr : (0 : ℝ) < z n := by exact_mod_cast hn
    simp [abs_of_pos hr, hr]
  · refine ⟨-1, by decide, ?_⟩
    filter_upwards [h] with n hn
    have hr : (z n : ℝ) < 0 := by exact_mod_cast hn
    simp [abs_of_neg hr, hr]

private theorem converges_of_rational_cuts (u : ℕ → ℝ)
    (hbdd : ∀ᶠ n in atTop, 0 ≤ u n ∧ u n ≤ 1)
    (hcut : ∀ r : ℚ, (∀ᶠ n in atTop, (r : ℝ) < u n) ∨ (∀ᶠ n in atTop, u n < r)) :
    ∃ limit : ℝ, Tendsto u atTop (𝓝 limit) := by
  let S : Set ℝ := {r | ∀ᶠ n in atTop, r < u n}
  have hS : S.Nonempty := by
    refine ⟨-1, ?_⟩
    filter_upwards [hbdd] with n hn using (by linarith [hn.1])
  have hS_bdd : BddAbove S := by
    refine ⟨1, fun r hr ↦ ?_⟩
    have h := (hbdd.and hr).exists
    obtain ⟨n, hn, hrn⟩ := h
    exact (hrn.trans_le hn.2).le
  refine ⟨sSup S, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro r hr
    obtain ⟨t, ht, hrt⟩ := exists_lt_of_lt_csSup hS hr
    exact (show ∀ᶠ n in atTop, t < u n from ht).mono fun _ hn ↦ hrt.trans hn
  · intro r hr
    obtain ⟨q, hq, hqr⟩ := exists_rat_btwn hr
    rcases hcut q with hlo | hhi
    · exact (not_lt_of_ge (le_csSup hS_bdd hlo) hq).elim
    · exact hhi.mono fun _ hn ↦ hn.trans hqr

/-- Stable signs of all integer projections give a projection of arbitrarily small normalized size. -/
theorem exists_small_projection (b : ℕ → Fin 2 → ℤ)
    (hsign : ∀ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) →
      ((∀ᶠ n in atTop, 0 < p * b n 0 + q * b n 1) ∨
        (∀ᶠ n in atTop, p * b n 0 + q * b n 1 < 0)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ p q : ℤ, (p ≠ 0 ∨ q ≠ 0) ∧
      ∀ᶠ n in atTop, |(↑(p * b n 0 + q * b n 1) : ℝ)| ≤
        eps * (|(b n 0 : ℝ)| + |(b n 1 : ℝ)|) := by
  obtain ⟨sx, hsx, hxs⟩ := fixed_sign (fun n ↦ b n 0) (by
    simpa using hsign 1 0 (Or.inl one_ne_zero))
  obtain ⟨sy, hsy, hys⟩ := fixed_sign (fun n ↦ b n 1) (by
    simpa using hsign 0 1 (Or.inr one_ne_zero))
  let size (n : ℕ) : ℝ := |(b n 0 : ℝ)| + |(b n 1 : ℝ)|
  let ratio (n : ℕ) : ℝ := |(b n 0 : ℝ)| / size n
  have hpos : ∀ᶠ n in atTop, 0 < size n :=
    hxs.mono fun n hn ↦ add_pos_of_pos_of_nonneg hn.1 (abs_nonneg _)
  have hbdd : ∀ᶠ n in atTop, 0 ≤ ratio n ∧ ratio n ≤ 1 := by
    filter_upwards [hpos] with n hn
    exact ⟨div_nonneg (abs_nonneg _) hn.le,
      (div_le_one hn).2 (le_add_of_nonneg_right (abs_nonneg _))⟩
  have hcoeff (j k : ℤ) (hk : 0 < k) :
      (k - j) * sx ≠ 0 ∨ -j * sy ≠ 0 := by
    by_cases hj : j = 0
    · exact Or.inl (mul_ne_zero (by simpa [hj] using hk.ne') hsx)
    · exact Or.inr (mul_ne_zero (neg_ne_zero.mpr hj) hsy)
  have hprojection (j k : ℤ) : ∀ᶠ n in atTop,
      (↑((k - j) * sx * b n 0 + (-j * sy) * b n 1) : ℝ) =
        ((k : ℝ) * ratio n - (j : ℝ)) * size n := by
    filter_upwards [hpos, hxs, hys] with n hn hx hy
    have hratio : ratio n * size n = |(b n 0 : ℝ)| :=
      div_mul_cancel₀ _ hn.ne'
    push_cast
    calc
      ((k : ℝ) - j) * sx * b n 0 + (-j * sy) * b n 1 =
          (k : ℝ) * |(b n 0 : ℝ)| - (j : ℝ) * size n := by
        rw [show size n = |(b n 0 : ℝ)| + |(b n 1 : ℝ)| from rfl, ← hx.2, ← hy.2]
        ring
      _ = _ := by rw [sub_mul, mul_assoc, hratio]
  have hcut (r : ℚ) :
      (∀ᶠ n in atTop, (r : ℝ) < ratio n) ∨ (∀ᶠ n in atTop, ratio n < r) := by
    let j : ℤ := r.num
    let k : ℤ := r.den
    have hk : 0 < k := by
      change (0 : ℤ) < (r.den : ℤ)
      exact_mod_cast r.pos
    have hkr : (0 : ℝ) < k := Int.cast_pos.mpr hk
    have hr : (r : ℝ) = (j : ℝ) / (k : ℝ) := by
      simp only [j, k, Rat.cast_def, Int.cast_natCast]
    rcases hsign ((k - j) * sx) (-j * sy) (hcoeff j k hk) with hp | hp
    · left
      filter_upwards [hpos, hprojection j k, hp] with n hsize hproj hn
      have hp' : (0 : ℝ) < (↑((k - j) * sx * b n 0 + (-j * sy) * b n 1) : ℝ) := by
        exact_mod_cast hn
      have hlinear : 0 < (k : ℝ) * ratio n - (j : ℝ) :=
        pos_of_mul_pos_left (hproj ▸ hp') hsize.le
      rw [hr, div_lt_iff₀ hkr, mul_comm]
      exact sub_pos.mp hlinear
    · right
      filter_upwards [hpos, hprojection j k, hp] with n hsize hproj hn
      have hp' : (↑((k - j) * sx * b n 0 + (-j * sy) * b n 1) : ℝ) < 0 := by
        exact_mod_cast hn
      have hlinear : (k : ℝ) * ratio n - (j : ℝ) < 0 :=
        neg_of_mul_neg_left (hproj ▸ hp') hsize.le
      rw [hr, lt_div_iff₀ hkr, mul_comm]
      exact sub_neg.mp hlinear
  obtain ⟨limit, hlim⟩ := converges_of_rational_cuts ratio hbdd hcut
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / eps)
  have hN_pos : 0 < N := Nat.cast_pos.mp ((by positivity : 0 < 1 / eps).trans hN)
  obtain ⟨j, k, hk, _, happ⟩ := Real.exists_int_int_abs_mul_sub_le limit hN_pos
  have hsmall : |(k : ℝ) * limit - (j : ℝ)| < eps := by
    refine happ.trans_lt ((div_lt_iff₀ (by positivity)).2 ?_)
    have hprod := (div_lt_iff₀ heps).1 (hN.trans (lt_add_one (N : ℝ)))
    simpa only [mul_comm] using hprod
  have hnear : ∀ᶠ n in atTop, |(k : ℝ) * ratio n - (j : ℝ)| < eps :=
    (tendsto_order.1 ((hlim.const_mul (k : ℝ)).sub_const (j : ℝ)).abs).2 eps hsmall
  refine ⟨(k - j) * sx, -j * sy, hcoeff j k hk, ?_⟩
  filter_upwards [hpos, hprojection j k, hnear] with n hn hproj hbound
  change |(↑((k - j) * sx * b n 0 + (-j * sy) * b n 1) : ℝ)| ≤ eps * size n
  rw [hproj, abs_mul, abs_of_pos hn]
  exact mul_le_mul_of_nonneg_right hbound.le hn.le

end OMA.ER193

namespace OMA

private lemma erdos193_linear_fiber_collinear (p q : ℚ) (hpq : p ≠ 0 ∨ q ≠ 0)
    (a : Fin 2 → ℚ) :
    Collinear ℚ {x : Fin 2 → ℚ | p * x 0 + q * x 1 = p * a 0 + q * a 1} := by
  rw [collinear_iff_of_mem (show a ∈ {x : Fin 2 → ℚ |
    p * x 0 + q * x 1 = p * a 0 + q * a 1} from rfl)]
  refine ⟨![-q, p], ?_⟩
  intro x hx
  change p * x 0 + q * x 1 = p * a 0 + q * a 1 at hx
  rcases hpq with hp | hq
  · let r := (x 1 - a 1) / p
    have hr : r * p = x 1 - a 1 := div_mul_cancel₀ _ hp
    refine ⟨r, ?_⟩
    funext i
    fin_cases i
    · change x 0 = r * (-q) + a 0
      apply mul_left_cancel₀ hp
      linear_combination hx + q * hr
    · change x 1 = r * p + a 1
      linear_combination -hr
  · let r := (a 0 - x 0) / q
    have hr : r * q = a 0 - x 0 := div_mul_cancel₀ _ hq
    refine ⟨r, ?_⟩
    funext i
    fin_cases i
    · change x 0 = r * (-q) + a 0
      linear_combination hr
    · change x 1 = r * p + a 1
      apply mul_left_cancel₀ hq
      linear_combination hx - p * hr

/-- Three indices in the same fiber of a nonzero form cannot be pairwise distinct. -/
lemma erdos193_fiber_repeat (b : ℕ → Fin 2 → ℤ) (hb : Function.Injective b)
    (hno : ¬ Erdos193.HasCollinearTriple ℚ (Set.range (fun n ↦ (↑) ∘ (b n) : ℕ → Fin 2 → ℚ)))
    (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) {i j k : ℕ}
    (hij : p * b i 0 + q * b i 1 = p * b j 0 + q * b j 1)
    (hik : p * b i 0 + q * b i 1 = p * b k 0 + q * b k 1) :
    i = j ∨ j = k ∨ i = k := by
  by_contra! hdistinct
  let B : ℕ → Fin 2 → ℚ := fun n ↦ (↑) ∘ (b n)
  have hinj : Function.Injective B := by
    intro m n h
    apply hb
    funext t
    have ht := congrFun h t
    change (b m t : ℚ) = (b n t : ℚ) at ht
    exact_mod_cast ht
  have hpq' : (p : ℚ) ≠ 0 ∨ (q : ℚ) ≠ 0 := by exact_mod_cast hpq
  have hij' : (p : ℚ) * B i 0 + q * B i 1 = p * B j 0 + q * B j 1 := by
    dsimp [B, Function.comp_def]
    exact_mod_cast hij
  have hik' : (p : ℚ) * B i 0 + q * B i 1 = p * B k 0 + q * B k 1 := by
    dsimp [B, Function.comp_def]
    exact_mod_cast hik
  apply hno
  refine ⟨B i, ⟨i, rfl⟩, B j, ⟨j, rfl⟩, B k, ⟨k, rfl⟩,
    hinj.ne hdistinct.1, hinj.ne hdistinct.2.1, hinj.ne hdistinct.2.2, ?_⟩
  apply (erdos193_linear_fiber_collinear p q hpq' (B i)).subset
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rfl
  · exact hij'.symm
  · exact hik'.symm

end OMA

theorem OMA.solution : type_of% @Erdos193.erdos_193_z2 := by
  intro S hS a ha hainf
  let normStep (d : Fin 2 → ℤ) := max |d 0| |d 1|
  obtain ⟨C, hC⟩ := (hS.image normStep).bddAbove
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hstep n i : |a (n+1) i - a n i| ≤ M := by
    have hbound : normStep (a (n+1) - a n) ≤ C :=
      hC (Set.mem_image_of_mem normStep (ha n))
    refine le_trans ?_ (hbound.trans (le_max_left _ _))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  obtain ⟨b, hbinj, hba, hbstep⟩ := OMA.Erdos193.bounded_step_injective_ray a hainf M hM hstep
  by_contra h
  have hsub : Set.range (fun n ↦ (↑) ∘ b n : ℕ → Fin 2 → ℚ) ⊆
      Set.range (fun n ↦ (↑) ∘ a n : ℕ → Fin 2 → ℚ) := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨m, hm⟩ := hba (Set.mem_range_self n)
    exact ⟨m, congrArg (fun v : Fin 2 → ℤ ↦ fun i ↦ (v i : ℚ)) hm⟩
  have hnob : ¬ Erdos193.HasCollinearTriple ℚ (Set.range (fun n ↦ (↑) ∘ b n : ℕ → Fin 2 → ℚ)) := by
    rintro ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hcol⟩
    exact h ⟨x, hsub hx, y, hsub hy, z, hsub hz, hxy, hyz, hxz, hcol⟩
  have hsparse (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
      SparseProjection (fun n ↦ p*b n 0 + q*b n 1) :=
    fun i j k hij hjk ↦ OMA.erdos193_fiber_repeat b hbinj hnob p q hpq hij (hij.trans hjk)
  have hsign (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
      (∀ᶠ n in atTop, 0 < p*b n 0 + q*b n 1) ∨
      (∀ᶠ n in atTop, p*b n 0 + q*b n 1 < 0) :=
    eventually_projection_sign (hsparse p q hpq) (by positivity) (projection_step b hbstep p q)
  let R := max (max (normStep (b 0)) M) 1
  have hR : 0 < (R : ℝ) := by
    exact_mod_cast (show (0 : ℤ) < R from lt_of_lt_of_le Int.zero_lt_one (le_max_right _ _))
  have hMR : M ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR0 (i : Fin 2) : |b 0 i| ≤ R := by
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_left _ _))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  let ε := 1 / (16 * (R : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨p, q, hpq, hsmall⟩ := OMA.ER193.exists_small_projection b hsign ε hε
  apply slow_projection_impossible (hsparse p q hpq)
  filter_upwards [hsmall] with n hn
  have bound (i : Fin 2) : |((b n i : ℤ) : ℝ)| ≤ (R : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast coordinate_growth b (fun j i ↦ (hbstep j i).trans hMR) hR0 n i
  have hsum : |((b n 0 : ℤ) : ℝ)| + |((b n 1 : ℤ) : ℝ)| ≤ 2*(R : ℝ)*((n : ℝ)+1) := by
    linarith [bound 0, bound 1]
  calc
    _ ≤ ε * (|((b n 0 : ℤ) : ℝ)| + |((b n 1 : ℤ) : ℝ)|) := hn
    _ ≤ ε * (2*(R : ℝ)*((n : ℝ)+1)) := mul_le_mul_of_nonneg_left hsum hε.le
    _ = _ := by dsimp [ε]; field_simp; ring
