import OMAReductions.R_Erdos704_erdos_704_variants_larman_rogers_R1
import Mathlib.Data.ZMod.Basic

/-!
# A discrete periodic Voronoi construction

Pack centres on a periodic integer grid and assign each grid point to a nearest
centre. Shrink each Voronoi cell by a rational factor below one third. On a
refined grid, each old point contributes a small block of points. Within - cell
diameters and between - cell distances are separated from the forbidden distance.
The geometry is the Euclidean construction of Prosanov (arXiv:1610.02846).
-/

namespace OMA.LarmanRogersGrid

open Finset Filter InnerProductSpace
open scoped Topology

private abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Lattice (n : ℕ) := Fin n → ℤ
private abbrev Grid (n m : ℕ) := Fin n → ZMod m

private def embed (n : ℕ) : Lattice n →+ Space n where
  toFun p := WithLp.toLp 2 (fun i => (p i : ℝ))
  map_zero' := by ext i; simp
  map_add' p q := by ext i; simp

private theorem embed_apply {n : ℕ} (p : Lattice n) (i : Fin n) :
    embed n p i = (p i : ℝ) := rfl

private theorem embed_nsmul {n : ℕ} (a : ℕ) (p : Lattice n) :
    embed n (a • p) = (a : ℝ) • embed n p := by
  ext i
  simp [embed_apply, nsmul_eq_mul]

private def residue {n : ℕ} (m : ℕ) : Lattice n →+ Grid n m where
  toFun p i := (p i : ZMod m)
  map_zero' := by ext i; simp
  map_add' p q := by ext i; simp

private theorem residue_apply {n m : ℕ} (p : Lattice n) (i : Fin n) :
    residue m p i = (p i : ZMod m) := rfl

private def repr {n m : ℕ} (p : Grid n m) : Lattice n := fun i => (p i).val

private theorem residue_repr {n m : ℕ} [NeZero m] (p : Grid n m) :
    residue m (repr p) = p := by
  funext i
  simp [repr, residue_apply]

private theorem residue_period {n m : ℕ} (p z : Lattice n) :
    residue m (p + m • z) = residue m p := by
  funext i
  simp [residue_apply, nsmul_eq_mul]

private theorem residue_congr {n m : ℕ} {p q : Lattice n}
    (h : residue m p = residue m q) : ∃ z : Lattice n, q = p + m • z := by
  have hi (i : Fin n) : ∃ z : ℤ, q i - p i = (m : ℤ) * z :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun h i)
  choose z hz using hi
  refine ⟨z, ?_⟩
  funext i
  change q i = p i + (m : ℤ) * z i
  linarith [hz i]

private theorem norm_coord_bound {n : ℕ} (x : Space n) (B : ℝ)
    (hB : ∀ i, |x i| ≤ B) : ‖x‖ ≤ n * B := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hx : (∑ i, x i • b i) = x := by
    simpa [b, EuclideanSpace.basisFun_repr] using b.sum_repr x
  calc
    ‖x‖ = ‖∑ i, x i • b i‖ := congrArg norm hx.symm
    _ ≤ ∑ i, ‖x i • b i‖ := norm_sum_le _ _
    _ = ∑ i, |x i| := by simp [norm_smul, b.norm_eq_one, Real.norm_eq_abs]
    _ ≤ ∑ _ : Fin n, B := sum_le_sum fun i _ => hB i
    _ = _ := by simp [nsmul_eq_mul]

private theorem sep_of_same_residue {n m : ℕ} (hm : 0 < m)
    {p q : Lattice n} (hr : residue (2 * m) p = residue (2 * m) q) (hne : p ≠ q) :
    (3 : ℝ) / 2 * m < dist (embed n p) (embed n q) := by
  obtain ⟨z, hz⟩ := residue_congr hr
  have hnz : z ≠ 0 := by
    intro he
    subst z
    exact hne (by simpa using hz.symm)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hnz
  have hzi : z i ≠ 0 := hi
  have hZ : (1 : ℝ) ≤ |(z i : ℝ)| := by
    have hsign : 1 ≤ z i ∨ z i ≤ -1 := by omega
    rcases hsign with h | h
    · exact (by exact_mod_cast h : (1 : ℝ) ≤ z i).trans (le_abs_self _)
    · have hn : (z i : ℝ) ≤ -1 := by exact_mod_cast h
      exact (by linarith : (1 : ℝ) ≤ -(z i : ℝ)).trans (neg_le_abs _)
  have hcoord : |embed n z i| ≤ ‖embed n z‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (embed n z) i
  have hnorm : 1 ≤ ‖embed n z‖ := hZ.trans (by simpa [embed_apply] using hcoord)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd : dist (embed n p) (embed n q) = (2 * (m : ℝ)) * ‖embed n z‖ := by
    rw [hz, map_add, embed_nsmul, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
  rw [hd]
  nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * (m : ℝ) by positivity)]

private theorem shrink_separation {n : ℕ} {x y c d : Space n} {a b : ℝ}
    (ha : 0 ≤ a) (hx : dist x c ≤ dist x d) (hy : dist y d ≤ dist y c) :
    b * dist c d ≤ dist (a • x + b • c) (a • y + b • d) := by
  by_cases hcd : c = d
  · subst d
    simp
  have hx' := pow_le_pow_left₀ dist_nonneg hx 2
  have hy' := pow_le_pow_left₀ dist_nonneg hy 2
  simp only [dist_eq_norm, norm_sub_sq_real] at hx' hy'
  have hinner : 0 ≤ inner ℝ (x - y) (c - d) := by
    simp only [inner_sub_left, inner_sub_right]
    linarith
  let w := c - d
  have hw : 0 < ‖w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcd)
  have hEq : (a • x + b • c) - (a • y + b • d) = a • (x - y) + b • w := by
    dsimp [w]
    module
  rw [dist_eq_norm, dist_eq_norm, hEq]
  have hineq := real_inner_le_norm (a • (x - y) + b • w) w
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hineq
  change b * ‖w‖ ≤ ‖a • (x - y) + b • w‖
  apply (mul_le_mul_iff_left₀ hw).mp
  nlinarith [mul_nonneg ha hinner]

private theorem shrink_within {n : ℕ} {x y c : Space n} {a b R : ℝ}
    (ha : 0 ≤ a) (hx : dist x c ≤ R) (hy : dist y c ≤ R) :
    dist (a • x + b • c) (a • y + b • c) ≤ 2 * a * R := by
  have hxy : dist x y ≤ 2 * R := by
    linarith [dist_triangle x c y, dist_comm c y]
  rw [dist_add_right, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
    ← dist_eq_norm]
  nlinarith [mul_le_mul_of_nonneg_left hxy ha]

private theorem dist_embed_translate {n : ℕ} (p q z : Lattice n) :
    dist (embed n (p + z)) (embed n (q + z)) = dist (embed n p) (embed n q) := by
  rw [map_add, map_add, dist_add_right]

private def Separated {n m : ℕ} (C : Finset (Grid n (2 * m))) : Prop :=
  ∀ p q : Lattice n, residue (2 * m) p ∈ C → residue (2 * m) q ∈ C → p ≠ q →
    (3 : ℝ) / 2 * m < dist (embed n p) (embed n q)

private theorem packing_centres (n m : ℕ) (hm : 0 < m) :
    ∃ C : Finset (Grid n (2 * m)), Separated C ∧
      ∀ p : Lattice n, ∃ c : Lattice n, residue (2 * m) c ∈ C ∧
        dist (embed n p) (embed n c) ≤ (3 : ℝ) / 2 * m := by
  classical
  let : NeZero (2 * m) := ⟨by omega⟩
  let A := (univ : Finset (Grid n (2 * m))).powerset.filter Separated
  have hex : A.Nonempty := ⟨∅, mem_filter.mpr
    ⟨mem_powerset.mpr (subset_univ _), by simp [Separated]⟩⟩
  obtain ⟨C, hCA, hmax⟩ := A.exists_max_image Finset.card hex
  have hs : Separated C := (mem_filter.mp hCA).2
  refine ⟨C, hs, fun p => ?_⟩
  by_contra! hFar
  have hp : residue (2 * m) p ∉ C := by
    intro hp
    have hn : (0 : ℝ) ≤ 3 / 2 * m := by positivity
    exact hn.not_gt (by simpa using hFar p hp)
  let C' := insert (residue (2 * m) p) C
  have hNew {x y : Lattice n} (hx : residue (2 * m) x = residue (2 * m) p)
      (hy : residue (2 * m) y ∈ C) : (3 : ℝ) / 2 * m < dist (embed n x) (embed n y) := by
    obtain ⟨z, hxz⟩ := residue_congr hx.symm
    let y' := y - (2 * m) • z
    have hyy : y' + (2 * m) • z = y := sub_add_cancel _ _
    have hres := residue_period (m := 2 * m) y' z
    rw [hyy] at hres
    have hdy := dist_embed_translate p y' ((2 * m) • z)
    rw [← hxz, hyy] at hdy
    rw [hdy]
    exact hFar y' (hres ▸ hy)
  have hSep : Separated C' := by
    intro x y hx hy hne
    rcases mem_insert.mp hx with hx | hx
    · rcases mem_insert.mp hy with hy | hy
      · exact sep_of_same_residue hm (hx.trans hy.symm) hne
      · exact hNew hx hy
    · rcases mem_insert.mp hy with hy | hy
      · rw [dist_comm]
        exact hNew hy hx
      · exact hs x y hx hy hne
  have hCard := hmax C' (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hSep⟩)
  rw [show C'.card = C.card + 1 from card_insert_of_notMem hp] at hCard
  omega

private def lattice_sq {n : ℕ} (p q : Lattice n) : ℕ :=
  ∑ i, (p i - q i).natAbs ^ 2

private theorem dist_embed_sq {n : ℕ} (p q : Lattice n) :
    dist (embed n p) (embed n q) ^ 2 = (lattice_sq p q : ℝ) := by
  rw [dist_eq_norm, ← map_sub, PiLp.norm_sq_eq_of_L2]
  simp [lattice_sq, embed_apply, Real.norm_eq_abs, sq_abs, Nat.cast_sum, Nat.cast_natAbs,
    Int.cast_abs]

private structure Nearest {n m : ℕ} (C : Finset (Grid n (2 * m))) (p c : Lattice n) : Prop where
  mem : residue (2 * m) c ∈ C
  close : dist (embed n p) (embed n c) ≤ (3 : ℝ) / 2 * m
  minimal : ∀ z : Lattice n, residue (2 * m) z ∈ C →
    dist (embed n p) (embed n c) ≤ dist (embed n p) (embed n z)

private theorem exists_nearest {n m : ℕ} (C : Finset (Grid n (2 * m))) (p c₀ : Lattice n)
    (hc₀ : residue (2 * m) c₀ ∈ C) (hclose : dist (embed n p) (embed n c₀) ≤ (3 : ℝ) / 2 * m) :
    ∃ c, Nearest C p c := by
  classical
  let P (k : ℕ) := ∃ c : Lattice n, residue (2 * m) c ∈ C ∧ lattice_sq p c = k
  have hP : ∃ k, P k := ⟨lattice_sq p c₀, c₀, hc₀, rfl⟩
  obtain ⟨c, hc, he⟩ := Nat.find_spec hP
  have hMin (z : Lattice n) (hz : residue (2 * m) z ∈ C) :
      dist (embed n p) (embed n c) ≤ dist (embed n p) (embed n z) := by
    have h := Nat.find_min' hP (show P (lattice_sq p z) from ⟨z, hz, rfl⟩)
    have hsq : dist (embed n p) (embed n c) ^ 2 ≤ dist (embed n p) (embed n z) ^ 2 := by
      rw [dist_embed_sq, dist_embed_sq, he]
      exact_mod_cast h
    exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp hsq
  exact ⟨c, hc, (hMin c₀ hc₀).trans hclose, hMin⟩

private theorem Nearest.period {n m : ℕ} {C : Finset (Grid n (2 * m))} {p c : Lattice n}
    (h : Nearest C p c) (z : Lattice n) :
    Nearest C (p + (2 * m) • z) (c + (2 * m) • z) := by
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · rw [residue_period]
    exact h.mem
  · rw [dist_embed_translate]
    exact h.close
  · let y' := y - (2 * m) • z
    have he : y' + (2 * m) • z = y := sub_add_cancel _ _
    have hu := residue_period (m := 2 * m) y' z
    rw [he] at hu
    have hy' : residue (2 * m) y' ∈ C := hu ▸ hy
    rw [dist_embed_translate]
    have hd := dist_embed_translate p y' ((2 * m) • z)
    rw [he] at hd
    rw [hd]
    exact h.minimal y' hy'

private def contract {n : ℕ} (a : ℕ) (p c : Lattice n) : Lattice n :=
  a • p + (2 * a + 1) • c

private theorem embed_contract {n : ℕ} (a : ℕ) (p c : Lattice n) :
    embed n (contract a p c) = (a : ℝ) • embed n p + (2 * (a : ℝ) + 1) • embed n c := by
  rw [contract, map_add, embed_nsmul, embed_nsmul]
  push_cast
  rfl

private theorem contract_period {n : ℕ} (a m : ℕ) (p c z r : Lattice n) :
    contract a (p + (2 * m) • z) (c + (2 * m) • z) + r =
      contract a p c + r + (2 * m * (3 * a + 1)) • z := by
  funext i
  change (a : ℤ) * (p i + (2 * m : ℕ) * z i) + (2 * a + 1 : ℕ) * (c i + (2 * m : ℕ) * z i) + r i =
    (a : ℤ) * p i + (2 * a + 1 : ℕ) * c i + r i + (2 * m * (3 * a + 1):ℕ) * z i
  push_cast
  ring

private theorem scaled_gap {n m a : ℕ} {C : Finset (Grid n (2 * m))}
    (hLarge : 4 * (n : ℝ) * ((a : ℝ) + 1) < m)
    (hS : Separated C) {p q c d : Lattice n}
    (hP : Nearest C p c) (hQ : Nearest C q d)
    {X Y : Space n}
    (hX : dist X (embed n (contract a p c)) ≤ n * ((a : ℝ) + 1))
    (hY : dist Y (embed n (contract a q d)) ≤ n * ((a : ℝ) + 1)) :
    (c = d → dist X Y < (m : ℝ) * (3 * a + 1)) ∧
      (c ≠ d → (m : ℝ) * (3 * a + 1) < dist X Y) := by
  have hm : 0 < (m : ℝ) := lt_of_le_of_lt (by positivity) hLarge
  let U := embed n (contract a p c)
  let V := embed n (contract a q d)
  change dist X U ≤ _ at hX
  change dist Y V ≤ _ at hY
  have hUp := dist_triangle4_right X Y U V
  have hDown := dist_triangle4_right U V X Y
  rw [dist_comm U X, dist_comm V Y] at hDown
  constructor
  · intro h
    subst d
    have hup : dist U V ≤ 2 * (a : ℝ) * (3 / 2 * m) := by
      dsimp [U, V]
      rw [embed_contract, embed_contract]
      exact shrink_within (Nat.cast_nonneg _) hP.close hQ.close
    nlinarith
  · intro h
    have hlow : (2 * (a : ℝ) + 1) * (3 / 2 * m) < dist U V := by
      dsimp [U, V]
      rw [embed_contract, embed_contract]
      exact (mul_lt_mul_of_pos_left (hS c d hP.mem hQ.mem h) (by positivity)).trans_le
        (shrink_separation (Nat.cast_nonneg _) (hP.minimal d hQ.mem) (hQ.minimal c hP.mem))
    nlinarith

private def digits {n a : ℕ} (r : Fin n → Fin a) : Lattice n := fun i => (r i).val

private theorem digits_near {n a : ℕ} (u : Lattice n) (r : Fin n → Fin a) :
    dist (embed n (u + digits r)) (embed n u) ≤ (n : ℝ) * a := by
  rw [map_add, dist_eq_norm, add_sub_cancel_left]
  apply norm_coord_bound
  intro i
  have hi : ((r i).val : ℝ) ≤ a := by exact_mod_cast (r i).isLt.le
  rw [embed_apply]
  change |(((r i).val : ℤ) : ℝ)| ≤ a
  rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hi

private theorem digits_unique {n a : ℕ} {p q : Lattice n}
    {r s : Fin n → Fin a} (he : a • p + digits r = a • q + digits s) :
    p = q ∧ r = s := by
  have hcoord (i : Fin n) :
      (a : ℤ) * (p i) + ((r i).val : ℤ) = (a : ℤ) * (q i) + ((s i).val : ℤ) := congrFun he i
  have hP (i : Fin n) : p i = q i := by
    have hr0 : (0 : ℤ) ≤ (r i).val := by positivity
    have hs0 : (0 : ℤ) ≤ (s i).val := by positivity
    have hr : ((r i).val : ℤ) < a := by exact_mod_cast (r i).isLt
    have hs : ((s i).val : ℤ) < a := by exact_mod_cast (s i).isLt
    have h := hcoord i
    rcases lt_trichotomy (p i) (q i) with hlt | heq | hgt
    · have hd : (1 : ℤ) ≤ q i - p i := by omega
      have hMul := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℤ) a)
      linarith
    · exact heq
    · have hd : (1 : ℤ) ≤ p i - q i := by omega
      have hMul := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℤ) a)
      linarith
  refine ⟨funext hP, funext fun i => Fin.ext ?_⟩
  have h := hcoord i
  rw [hP i, add_left_cancel_iff] at h
  exact_mod_cast h

private theorem refinement_injective {n m a : ℕ} [NeZero (2 * m)]
    {C : Finset (Grid n (2 * m))}
    (hLarge : 4 * (n : ℝ) * ((a : ℝ) + 1) < m)
    (hS : Separated C) (centre : Grid n (2 * m) → Lattice n)
    (hc : ∀ p, Nearest C (repr p) (centre p)) :
    Function.Injective
      (fun v : Grid n (2 * m) × (Fin n → Fin a) =>
        residue (2 * m * (3 * a + 1)) (contract a (repr v.1) (centre v.1) + digits v.2)) := by
  rintro ⟨p, r⟩ ⟨q, s⟩ he
  let P := contract a (repr p) (centre p) + digits r
  let Q := contract a (repr q) (centre q) + digits s
  change residue (2 * m * (3 * a + 1)) P = residue (2 * m * (3 * a + 1)) Q at he
  obtain ⟨z, hz⟩ := residue_congr he.symm
  let q' := repr q + (2 * m) • z
  let d := centre q + (2 * m) • z
  have hd : Nearest C q' d := (hc q).period z
  have hEq : P = contract a q' d + digits s := hz.trans
    (contract_period a m (repr q) (centre q) z (digits s)).symm
  have hN : (n : ℝ) * a ≤ n * ((a : ℝ) + 1) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hCloseP := (digits_near (contract a (repr p) (centre p)) r).trans hN
  have hCloseQ := (digits_near (contract a q' d) s).trans hN
  have hec : centre p = d := by
    by_contra hne
    have h := (scaled_gap hLarge hS (hc p) hd hCloseP hCloseQ).2 hne
    change (m : ℝ) * (3 * a + 1) < dist (embed n P) (embed n (contract a q' d + digits s)) at h
    rw [← hEq, dist_self] at h
    have hm : 0 < (m : ℝ) := lt_of_le_of_lt (by positivity) hLarge
    exact (not_lt_of_ge (by positivity : 0 ≤ (m : ℝ) * (3 * a + 1))) h
  change contract a (repr p) (centre p) + digits r = contract a q' d + digits s at hEq
  rw [hec] at hEq
  have hDigits : a • repr p + digits r = a • q' + digits s := by
    simp only [contract] at hEq
    have hEq' :
        (a • repr p + digits r) + (2 * a + 1) • d = (a • q' + digits s) + (2 * a + 1) • d := by
      simpa only [add_assoc, add_comm, add_left_comm] using hEq
    exact add_right_cancel hEq'
  obtain ⟨hp, hr⟩ := digits_unique hDigits
  have hpq : p = q := by
    have he := congrArg (residue (2 * m)) hp
    simpa only [q', residue_period, residue_repr] using he
  exact Prod.ext hpq hr

private noncomputable def rounded {n : ℕ} (B : ℝ) (x : Space n) : Lattice n :=
  fun i => ⌊B * x i⌋

private theorem rounded_near {n : ℕ} (B : ℝ) (x : Space n) :
    dist (B • x) (embed n (rounded B x)) ≤ n := by
  rw [dist_eq_norm, ← mul_one (n : ℝ)]
  apply norm_coord_bound
  intro i
  change |B * x i - (⌊B * x i⌋ : ℤ)| ≤ (1 : ℝ)
  have hl := Int.floor_le (B * x i)
  have hu := Int.lt_floor_add_one (B * x i)
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  linarith

private theorem translate_rounding {n m a : ℕ}
    [NeZero (2 * m * (3 * a + 1))] {X : Space n}
    {t : Grid n (2 * m * (3 * a + 1))} {p c : Lattice n} (r : Fin n → Fin a)
    (h : residue (2 * m * (3 * a + 1)) (rounded ((m : ℝ) * (3 * a + 1)) X) - t =
      residue (2 * m * (3 * a + 1)) (contract a p c + digits r)) :
    ∃ z : Lattice n,
      dist (((m : ℝ) * (3 * a + 1)) • X - embed n (repr t))
        (embed n (contract a (p + (2 * m) • z) (c + (2 * m) • z))) ≤ n * ((a : ℝ) + 1) := by
  let M := 2 * m * (3 * a + 1)
  let B := (m : ℝ) * (3 * a + 1)
  let T := repr t
  have hcong : residue M (contract a p c + digits r + T) = residue M (rounded B X) := by
    rw [map_add, residue_repr, ← h, sub_add_cancel]
  obtain ⟨z, hz⟩ := residue_congr hcong
  refine ⟨z, ?_⟩
  let u := contract a (p + (2 * m) • z) (c + (2 * m) • z)
  have hraw : rounded B X = u + digits r + T := by
    rw [contract_period]
    exact hz.trans (add_right_comm _ _ _)
  have hNear := rounded_near B X
  rw [hraw, map_add] at hNear
  have ht : dist (B • X - embed n T) (embed n (u + digits r)) =
      dist (B • X) (embed n (u + digits r) + embed n T) := by
    rw [← dist_add_right (B • X - embed n T) (embed n (u + digits r)) (embed n T), sub_add_cancel]
  have he := dist_triangle (B • X - embed n T) (embed n (u + digits r)) (embed n u)
  rw [ht] at he
  have hd := digits_near u r
  change dist (B • X - embed n T) (embed n u) ≤ n * ((a : ℝ) + 1)
  nlinarith

private theorem card_grid (n M : ℕ) [NeZero M] : Fintype.card (Grid n M) = M ^ n := by
  simp [Grid, Fintype.card_pi, ZMod.card]

private theorem finite_motif (n m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    [NeZero (2 * m)] [NeZero (2 * m * (3 * a + 1))]
    (hLarge : 4 * (n : ℝ) * ((a : ℝ) + 1) < m) :
    ∃ (project : Space n → Grid n (2 * m * (3 * a + 1))) (S : Finset (Grid n (2 * m * (3 * a + 1)))),
      S.Nonempty ∧ S.card = (2 * m) ^ n * a ^ n ∧
      ∀ t x y, project x - t ∈ S → project y - t ∈ S → dist x y ≠ 1 := by
  classical
  obtain ⟨C, hSep, hCover⟩ := packing_centres n m hm
  have hExists (p : Grid n (2 * m)) : ∃ c, Nearest C (repr p) c := by
    obtain ⟨c, hc, hd⟩ := hCover (repr p)
    exact exists_nearest C (repr p) c hc hd
  choose c hc using hExists
  let M := 2 * m * (3 * a + 1)
  let B := (m : ℝ) * (3 * a + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let color (u : Grid n (2 * m) × (Fin n → Fin a)) : Grid n M :=
    residue M (contract a (repr u.1) (c u.1) + digits u.2)
  let S := (univ : Finset (Grid n (2 * m) × (Fin n → Fin a))).image color
  let project (x : Space n) : Grid n M := residue M (rounded B x)
  refine ⟨project, S, ?_, ?_, ?_⟩
  · exact ⟨color (0, fun _ => ⟨0, ha⟩), mem_image_of_mem color (mem_univ _)⟩
  · have hi : Function.Injective color := refinement_injective hLarge hSep c hc
    rw [show S.card = (univ : Finset (Grid n (2 * m) × (Fin n → Fin a))).card from
      card_image_of_injective _ hi, card_univ, Fintype.card_prod, card_grid]
    simp [Fintype.card_pi]
  · intro t x y hx hy hDist
    obtain ⟨⟨p, r⟩, _, hp⟩ := mem_image.mp hx
    obtain ⟨⟨q, s⟩, _, hq⟩ := mem_image.mp hy
    let X := B • x - embed n (repr t)
    let Y := B • y - embed n (repr t)
    obtain ⟨z, hz⟩ := translate_rounding r hp.symm
    obtain ⟨w, hw⟩ := translate_rounding s hq.symm
    have h := scaled_gap hLarge hSep ((hc p).period z) ((hc q).period w) hz hw
    have hXY : dist X Y = B := by
      dsimp [X, Y]
      rw [dist_sub_right, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hB, ← dist_eq_norm, hDist, mul_one]
    by_cases he : c p + (2 * m) • z = c q + (2 * m) • w
    · have hlt := h.1 he
      change dist X Y < B at hlt
      rw [hXY] at hlt
      exact (lt_irrefl B) hlt
    · have hlt := h.2 he
      change B < dist X Y at hlt
      rw [hXY] at hlt
      exact (lt_irrefl B) hlt

set_option maxHeartbeats 600000 in
theorem solution :
    ∀ D > (3 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A)
        (project : Space n → A) (S : Finset A),
        S.Nonempty ∧
        Real.log (Fintype.card A : ℝ) ≤ (n : ℝ) ^ 3 ∧
        (Fintype.card A : ℝ) / S.card ≤ D ^ n ∧
        ∀ (t : A) (x y : Space n), project x - t ∈ S → project y - t ∈ S → dist x y ≠ 1 := by
  intro D hD
  obtain ⟨a, ha⟩ := exists_nat_gt (max 1 (D - 3)⁻¹)
  have haR : 0 < (a : ℝ) :=
    (zero_lt_one.trans_le (le_max_left (1 : ℝ) _)).trans ha
  have haN : 0 < a := by exact_mod_cast haR
  have hD' : 0 < D - 3 := sub_pos.mpr hD
  have hProd : 1 < (D - 3) * (a : ℝ) := calc
    _ = (D - 3) * (D - 3)⁻¹ := (mul_inv_cancel₀ hD'.ne').symm
    _ < _ := mul_lt_mul_of_pos_left ((le_max_right _ _).trans_lt ha) hD'
  have hRatio : ((3 * a + 1 : ℕ):ℝ) / (a : ℝ) ≤ D := by
    apply (div_le_iff₀ haR).2
    push_cast
    nlinarith
  let K : ℕ := 16 * (a + 1) * (3 * a + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [eventually_ge_atTop (2 * K)] with n hn
  let m := 8 * (a + 1) * (n + 1)
  let M := 2 * m * (3 * a + 1)
  have hm : 0 < m := by dsimp [m]; positivity
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hM : 0 < M := by dsimp [M]; positivity
  let : NeZero (2 * m) := ⟨by omega⟩
  let : NeZero M := ⟨hM.ne'⟩
  have hLarge : 4 * (n : ℝ) * ((a : ℝ) + 1) < m := by
    dsimp [m]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_nonneg (α := ℝ) a)]
  obtain ⟨project, S, hS, hSize, hAvoid⟩ := finite_motif n m a hm haN hLarge
  refine ⟨Grid n M, inferInstance, inferInstance, project, S, hS, ?_, ?_, hAvoid⟩
  · rw [card_grid, Nat.cast_pow, Real.log_pow]
    have hnR : (2 : ℝ) * (K:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hMval : (M:ℝ) = (K:ℝ) * ((n : ℝ) + 1) := by dsimp [M, m, K]; push_cast; ring
    have hMp : 0 < (M:ℝ) := by exact_mod_cast hM
    have hb : (M:ℝ) ≤ (n : ℝ) ^ 2 := by
      rw [hMval]
      calc
        _ ≤ (K:ℝ) * (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ = (n : ℝ) * (2 * (K:ℝ)) := by ring
        _ ≤ _ := by simpa [pow_two] using mul_le_mul_of_nonneg_left hnR (Nat.cast_nonneg (α := ℝ) n)
    calc
      _ ≤ (n : ℝ) * (M:ℝ) :=
        mul_le_mul_of_nonneg_left ((Real.log_le_sub_one_of_pos hMp).trans (by linarith))
          (Nat.cast_nonneg _)
      _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = _ := by ring
  · rw [card_grid, hSize]
    push_cast
    have hcastM : (M:ℝ) = (2 * (m : ℝ)) * ((3 * a + 1 : ℕ):ℝ) := by dsimp [M]; push_cast; ring
    rw [hcastM, ← mul_pow, ← div_pow]
    have hnz : (2 * (m : ℝ)) ≠ 0 := by positivity
    rw [mul_div_mul_left _ _ hnz]
    exact pow_le_pow_left₀ (by positivity) hRatio n

end OMA.LarmanRogersGrid

theorem OMA.solution : OMA.R_Erdos704_erdos_704_variants_larman_rogers_R1.H1 :=
  OMA.LarmanRogersGrid.solution
