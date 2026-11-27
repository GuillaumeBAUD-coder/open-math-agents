import OMAReductions.R_Erdos147_erdos_147_variants_cubic_R1
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen

/-!
# Étape `H2` de la réduction R1 d'Erdős 147 (variante cubique)

Lemme 2.15 de Janzer (arXiv 2109.06110) : beaucoup de 4-cycles donnent un ensemble bon de
`8k`-cycles. Preuve (plan : `plan-h2.md`) : un sommet `v` et une classe dyadique de codegrés
(lemme 2.17 de l'article), puis une classe dyadique des multiplicités `h(x,z)` ; ensemble `D` de
triplets `(x,y,z)` tels que `v x y z` soit un 4-cycle. Les `8k`-cycles `x₀ y₀ x₁ y₁ ⋯` dont les
triplets `(x_i, y_i, x_(i+1))` sont dans `D` se comptent par la matrice `hmat D`
(`hmat D a b = #{y | (a,y,b) ∈ D}`) : Sidorenko porté par `N(v)`, bornes de conflit pondérées
(sommets répétés), à la place du lemme 2.18 (Morris–Saxton).
-/

-- Credit: @iLc0

open SimpleGraph Finset Filter Asymptotics Matrix
open scoped Classical

namespace E147H2

/-- Poids d'un uplet cyclique `x : Fin L → W` : produit des `M (x i) (x (i+1 mod L))`. -/
noncomputable def cycW {W : Type} [Fintype W] (M : Matrix W W ℝ) {L : ℕ} (x : Fin L → W) : ℝ :=
  ∏ i : Fin L, M (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩)

/-- Multiplicités d'un ensemble de triplets : `hmat D a b = #{y | (a, y, b) ∈ D}`. -/
noncomputable def hmat {W : Type} [Fintype W] (D : Finset (W × W × W)) : Matrix W W ℝ :=
  fun a b => (#(D.filter fun t => t.1 = a ∧ t.2.2 = b) : ℝ)

/-- Les triplets de `D` qui commencent par `a`. -/
noncomputable def rowSet {W : Type} (D : Finset (W × W × W)) (a : W) : Finset (W × W × W) :=
  D.filter fun t => t.1 = a

/-- Les milieux `y` des triplets `(a, y, z)` de `D`. -/
noncomputable def extSet {W : Type} (D : Finset (W × W × W)) (a : W) : Finset W :=
  (rowSet D a).image fun t => t.2.1

/-- Les `2m`-cycles injectifs `x₀ y₀ x₁ y₁ ⋯ x_(m-1) y_(m-1)` (positions `2i` et `2i+1`) dont
chaque triplet `(x_i, y_i, x_(i+1))` est dans `D`. -/
noncomputable def cycSet {W : Type} [Fintype W] (D : Finset (W × W × W)) (m : ℕ) :
    Finset (Fin (2 * m) → W) :=
  univ.filter fun w => Function.Injective w ∧ ∀ i : Fin m,
    (w ⟨2 * i.val, by have := i.isLt; omega⟩, w ⟨2 * i.val + 1, by have := i.isLt; omega⟩,
      w ⟨(2 * i.val + 2) % (2 * m), Nat.mod_lt _ (by have := i.isLt; omega)⟩) ∈ D

/- ## Déjà prouvés pour `H1` (repris de `h1-complet.lean`) -/

private def ext9 {W : Type} {n : ℕ} (x : Fin n → W) (z : W) (i : ℕ) : W :=
  if h : i < n then x ⟨i,h⟩ else z

private noncomputable def path9 {W : Type} [Fintype W] (M : Matrix W W ℝ)
    {n : ℕ} (x : Fin n → W) (z : W) : ℝ :=
  ∏ i : Fin n, M (ext9 x z i) (ext9 x z (i.val+1))

private def drop9 {W : Type} (n : ℕ) {s : ℕ} (x : Fin (s+n) → W) : Fin s → W :=
  fun i => x ⟨n+i.val, by omega⟩

private theorem cons9_val {W : Type} {n : ℕ} (a : W) (x : Fin n → W) (i : Fin (n+1))
    (j : Fin n) (h : i.val = j.val+1) : Fin.cons (α := fun _ => W) a x i = x j := by
  rw [show i = j.succ from Fin.ext h, Fin.cons_succ]

private theorem ext9_zero_cons {W : Type} {n : ℕ} (a z : W) (x : Fin n → W) :
    ext9 (Fin.cons a x) z 0 = a := by simp [ext9]

private theorem ext9_succ_cons {W : Type} {n : ℕ} (a z : W) (x : Fin n → W) (i : ℕ) :
    ext9 (Fin.cons a x) z (i+1) = ext9 x z i := by
  by_cases h : i < n
  · simp only [ext9, dif_pos (Nat.succ_lt_succ h), dif_pos h]
    exact cons9_val a x _ _ rfl
  · simp [ext9, h]

private theorem path9_cons {W : Type} [Fintype W] (M : Matrix W W ℝ)
    {n : ℕ} (a z : W) (x : Fin n → W) :
    path9 M (Fin.cons a x) z = M a (ext9 x z 0) * path9 M x z := by
  simp [path9, Fin.prod_univ_succ, ext9_zero_cons, ext9_succ_cons]

private theorem drop9_cons {W : Type} (s n : ℕ) (a : W) (x : Fin (s+n) → W) :
    drop9 (n+1) (Fin.cons a x) = drop9 n x := by
  funext i
  unfold drop9
  exact cons9_val a x _ _ (by dsimp; omega)

private theorem sumCons9 {W : Type} [Fintype W] {n : ℕ} (H : (Fin (n+1) → W) → ℝ) :
    ∑ x, H x = ∑ a, ∑ x, H (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => W)).sum_comp H, Fintype.sum_prod_type]
  rfl

private theorem cut9 {W : Type} [Fintype W] (M : Matrix W W ℝ) (s n : ℕ) (z : W)
    (H : W → (Fin s → W) → ℝ) :
    ∑ x : Fin (s+n) → W, path9 M x z * H (ext9 x z 0) (drop9 n x) =
    ∑ b, ∑ y : Fin s → W, path9 M y z * ((M^n) b (ext9 y z 0) * H b y) := by
  classical
  induction n generalizing H with
  | zero =>
    rw [sum_comm]
    have hd (x : Fin s → W) : drop9 0 x = x := by funext i; simp [drop9]
    simp [Matrix.one_apply, hd, mul_ite, ite_mul]
  | succ n ih =>
    refine (sumCons9 (n := s+n) (fun x => path9 M x z * H (ext9 x z 0) (drop9 (n+1) x))).trans ?_
    simp only [path9_cons, ext9_zero_cons, drop9_cons]
    apply sum_congr rfl
    intro b _
    calc
      _ = ∑ x : Fin (s+n) → W, path9 M x z *
          ((fun e y => M b e * H b y) (ext9 x z 0) (drop9 n x)) := by
        apply sum_congr rfl; intros; ring
      _ = _ := ih (fun e y => M b e * H b y)
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro y _
        rw [pow_succ', Matrix.mul_apply]
        simp only [sum_mul, mul_sum]
        apply sum_congr rfl
        intros
        ring

private theorem cyc9 {W : Type} [Fintype W] (M : Matrix W W ℝ) {n : ℕ}
    (x : Fin (n+1) → W) : cycW M x = path9 M x (x 0) := by
  apply prod_congr rfl
  intro i _
  simp only [ext9, dif_pos i.isLt]
  by_cases hi : i.val+1 < n+1
  · simp [hi, Nat.mod_eq_of_lt hi]
  · have he : i.val+1 = n+1 := by omega
    simp [he]

private theorem split9 {W : Type} [Fintype W] (M : Matrix W W ℝ)
    (L j l n m s : ℕ) (hL : L = 0+s+m+n+1) (hj : j = n+1)
    (hl : l = j+m) (hs : 0<s) (F : W → W → W → W → ℝ) :
    ∑ x : Fin L → W, cycW M x *
      F (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨j,by omega⟩) (x ⟨l,by omega⟩) =
    ∑ a, ∑ b, ∑ e, ∑ c, M a b * (M^n) b e * (M^m) e c * (M^s) c a * F a b e c := by
  subst L l j
  rw [sumCons9]
  apply sum_congr rfl
  intro a _
  let H := fun (b : W) (y : Fin (0+s+m) → W) =>
    M a b * F a b (ext9 y a 0) (ext9 (drop9 m y) a 0)
  calc
    _ = ∑ x : Fin (0+s+m+n) → W, path9 M x a * H (ext9 x a 0) (drop9 n x) := by
      apply sum_congr rfl
      intro x _
      rw [cyc9]
      simp only [Fin.cons_zero, path9_cons, H]
      have hpos : 0 < 0+s+m+n := by omega
      have hpos' : 0 < 0+s+m := by omega
      simp only [ext9, dif_pos hpos, dif_pos hpos', dif_pos (by omega : 0 < 0+s), drop9]
      simp only [Nat.add_zero]
      rw [cons9_val a x ⟨1,by omega⟩ ⟨0,hpos⟩ rfl,
        cons9_val a x ⟨n+1,by omega⟩ ⟨n,by omega⟩ rfl,
        cons9_val a x ⟨n+1+m,by omega⟩ ⟨n+m,by omega⟩ (by dsimp; omega)]
      rw [show (⟨0, by omega⟩ : Fin (0+s+m+n+1)) = 0 from rfl, Fin.cons_zero]
      ring
    _ = _ := cut9 M _ _ a H
    _ = _ := by
      apply sum_congr rfl
      intro b _
      change (∑ y : Fin (0+s+m) → W, path9 M y a *
        ((fun e t => (M^n) b e * (M a b * F a b e (ext9 t a 0)))
          (ext9 y a 0) (drop9 m y))) = _
      rw [cut9 M (0+s) m a (fun e t => (M^n) b e * (M a b * F a b e (ext9 t a 0)))]
      apply sum_congr rfl
      intro e _
      change (∑ t : Fin (0+s) → W, path9 M t a *
        ((fun c (_ : Fin 0 → W) => (M^m) e c * ((M^n) b e * (M a b * F a b e c)))
          (ext9 t a 0) (drop9 s t))) = _
      rw [cut9 M 0 s a (fun c _ => (M^m) e c * ((M^n) b e * (M a b * F a b e c)))]
      apply sum_congr rfl
      intro c _
      simp [path9, ext9]
      ring

/-- Découpe d'un uplet cyclique de longueur `2k` aux positions `0, 1, j, k+1`. -/
theorem cyc_split {W : Type} [Fintype W] (M : Matrix W W ℝ) (k j : ℕ) (hk : 2 ≤ k)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (F : W → W → W → W → ℝ) :
    ∑ x : Fin (2 * k) → W, cycW M x *
        F (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) (x ⟨j, by omega⟩) (x ⟨k + 1, by omega⟩) =
      ∑ a, ∑ b, ∑ e, ∑ c, M a b * (M ^ (j - 1)) b e * (M ^ (k + 1 - j)) e c *
        (M ^ (k - 1)) c a * F a b e c := by
  exact split9 M (2*k) j (k+1) (j-1) (k+1-j) (k-1)
    (by omega) (by omega) (by omega) (by omega) F

/-- Masse totale des uplets cycliques de longueur `2k`. -/
theorem total_cycW_eq_trace {W : Type} [Fintype W] (M : Matrix W W ℝ)
    (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W, cycW M x = trace (M ^ (2 * k)) := by
  classical
  calc
    _ = trace (M * (M ^ (1 - 1 : ℕ) * (M ^ (k + 1 - 1) * M ^ (k - 1)))) := by
      simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum,
        mul_one, mul_assoc] using cyc_split M k 1 hk le_rfl (by omega) (fun _ _ _ _ => 1)
    _ = _ := by
      simp only [← pow_add, ← pow_succ']
      congr 2
      omega

/-- Union sur les rotations : un conflit entre deux positions quelconques se ramène, par
rotation, à un conflit entre la position 0 et une position de `[1, k]`. -/
theorem bad_le_rot {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (r : W → W → Prop) (hr : ∀ u w, r u w → r w u) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ i j : Fin (2 * k), i ≠ j ∧ r (x i) (x j) then cycW M x else 0) ≤
      2 * k * ∑ x : Fin (2 * k) → W,
        (if ∃ j : Fin (2 * k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (x ⟨0, by omega⟩) (x j)
          then cycW M x else 0) := by
  classical
  let : NeZero (2 * k) := ⟨by omega⟩
  let I := Fin (2 * k)
  let rot (s : I) (x : I → W) := fun i : I ↦ x (i + s)
  let good (x : I → W) := ∃ j : I, 1 ≤ j.val ∧ j.val ≤ k ∧ r (x 0) (x j)
  let B (x : I → W) : ℝ := if good x then cycW M x else 0
  have cycpos (x : I → W) : 0 ≤ cycW M x := prod_nonneg fun _ _ ↦ hM ..
  have bpos (x : I → W) : 0 ≤ B x := by dsimp [B]; split <;> simp_all only [le_refl]
  let δ : I := ⟨1, by omega⟩
  have cyc (s : I) (x : I → W) : cycW M (rot s x) = cycW M x := by
    change (∏ i : I, M (x (i + s)) (x ((i + δ) + s))) = ∏ i : I, M (x i) (x (i + δ))
    simp_rw [add_right_comm _ δ s]
    exact Equiv.prod_comp (Equiv.addRight s) (fun i : I ↦ M (x i) (x (i + δ)))
  have reindex (s : I) : ∑ x : I → W, B (rot s x) = ∑ x : I → W, B x := by
    exact Equiv.sum_comp ((Equiv.addRight s).symm.arrowCongr (Equiv.refl W)) B
  have ordered (x : I → W) (i j : I) (hlt : i.val < j.val) (hij : r (x i) (x j)) :
      ∃ s : I, good (rot s x) := by
    by_cases h : j.val - i.val ≤ k
    · let t : I := ⟨j.val - i.val, by have := j.isLt; omega⟩
      have ht : t + i = j := by
        apply Fin.ext
        rw [Fin.val_add_eq_ite]; dsimp [t]; split <;> have := j.isLt <;> omega
      exact ⟨i, t, by dsimp [t]; omega, h, by simpa [rot, ht] using hij⟩
    · let t : I := ⟨2 * k - j.val + i.val, by have := j.isLt; omega⟩
      have ht : t + j = i := by
        apply Fin.ext
        rw [Fin.val_add_eq_ite]; dsimp [t]; split <;> have := j.isLt <;> omega
      exact ⟨j, t, by dsimp [t]; have := j.isLt; omega, by dsimp [t]; omega,
        by simpa [rot, ht] using hr _ _ hij⟩
  change _ ≤ 2 * (k : ℝ) * ∑ x : I → W, B x
  calc
    _ ≤ ∑ x : I → W, ∑ s : I, B (rot s x) := by
      apply sum_le_sum
      intro x _
      split
      · rename_i hx
        obtain ⟨i, j, hne, hij⟩ := hx
        have hval : i.val ≠ j.val := fun h ↦ hne (Fin.ext h)
        obtain ⟨s, hs⟩ : ∃ s : I, good (rot s x) :=
          (lt_or_gt_of_ne hval).elim (fun h ↦ ordered x i j h hij) (fun h ↦ ordered x j i h (hr _ _ hij))
        calc
          cycW M x = B (rot s x) := by simp [B, hs, cyc]
          _ ≤ _ := single_le_sum (fun z _ ↦ bpos (rot z x)) (mem_univ s)
      · exact sum_nonneg fun _ _ ↦ bpos _
    _ = _ := by rw [sum_comm]; simp [reindex, I]

/- ## Lemme 17 : traces d'une matrice pondérée symétrique -/

/- ## Auxiliaires (modèle : `h1-complet.lean`, lemmes 12 et 13) -/

private theorem symm17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hsym : ∀ u v, M u v = M v u)
    (n : ℕ) (u v : W) : (M ^ n) u v = (M ^ n) v u := by
  have h : M.IsSymm := by
    ext a b
    exact hsym b a
  exact (h.pow n).apply v u

private theorem trip17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (k : ℕ) (hk : 2 ≤ k)
    (F : W → W → W → ℝ) :
    ∑ x : Fin (2*k) → W, cycW M x * F (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) =
    ∑ a, ∑ b, ∑ c, M a b * (M^k) b c * (M^(k-1)) c a * F a b c := by
  classical
  rw [cyc_split M k 1 hk (by omega) (by omega) (fun a b _ c => F a b c)]
  simp [Matrix.one_apply, mul_ite, ite_mul, sum_ite_irrel]

private theorem trace17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (p q : ℕ) :
    trace (M ^ (p+q)) = ∑ a, ∑ b, (M^p) a b * (M^q) b a := by
  simp only [pow_add, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem ratio17 {U V : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V) : V * (U / V) ≤ U := by
  by_cases h : V = 0
  · simp [h, hU]
  · exact le_of_eq (by field_simp)

private theorem upperFirst17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (R : ℝ) (hrow : ∀ a, ∑ b, M a b ≤ R) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2*k) → W, cycW M x *
      ((M^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) /
       (M^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩)) ≤
    R * trace (M ^ (2*(k-1))) := by
  classical
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg hM
  rw [trip17 M k hk (fun a b c => (P (k-1)) a c / (P k) b c),
    two_mul, trace17, mul_sum]
  apply sum_le_sum
  intro a _
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro c _
  calc
    _ ≤ ∑ b, M a b * ((P (k-1)) a c * (P (k-1)) c a) := by
      apply sum_le_sum
      intro b _
      have hh := mul_le_mul_of_nonneg_left (ratio17 (hn (k-1) a c) (hn k b c))
        (mul_nonneg (hM a b) (hn (k-1) c a))
      dsimp [P] at *
      linarith only [hh]
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (hrow a) (mul_nonneg (hn _ _ _) (hn _ _ _))

private theorem mass17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (r : W → W → Prop) (hr : ∀ u w, r u w → r w u) (s : ℝ)
    (hmass : ∀ b e, ∑ a, (if r e a then M b a else 0) ≤ s) (n : ℕ) (b e c : W) :
    ∑ a, (if r a e then M a b * (M^n) c a / (M^n) a c else 0) ≤ s := by
  classical
  calc
    _ ≤ ∑ a, (if r e a then M b a else 0) := by
      apply sum_le_sum
      intro a _
      rw [symm17 M hsym n c a]
      by_cases h : r a e
      · rw [if_pos h, if_pos (hr a e h), hsym a b, mul_div_assoc]
        exact mul_le_of_le_one_right (hM b a) (div_self_le_one _)
      · rw [if_neg h]
        split
        · exact hM b a
        · exact le_rfl
    _ ≤ s := hmass b e

private theorem upperOne17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (r : W → W → Prop) (hr : ∀ u w, r u w → r w u) (s : ℝ)
    (hmass : ∀ b e, ∑ a, (if r e a then M b a else 0) ≤ s)
    (k j : ℕ) (hk : 2 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∑ x : Fin (2*k) → W, cycW M x *
      (if r (x ⟨0,by omega⟩) (x ⟨j,by omega⟩) then
       (M^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       (M^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) else 0) ≤
    s * trace (M ^ (2*k)) := by
  classical
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg hM
  rw [cyc_split M k j hk hj hjk
    (fun a b e c => if r a e then (P k) b c / (P (k-1)) a c else 0),
    two_mul, trace17, mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  rw [mul_sum]
  let f := fun a e c : W => M a b * (P (j-1)) b e * (P (k+1-j)) e c *
    (P (k-1)) c a * (if r a e then (P k) b c / (P (k-1)) a c else 0)
  change (∑ a, ∑ e, ∑ c, f a e c) ≤ _
  have perm : (∑ a, ∑ e, ∑ c, f a e c) = ∑ c, ∑ e, ∑ a, f a e c := by
    calc
      _ = ∑ a, ∑ c, ∑ e, f a e c := sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
        |>.trans (sum_congr rfl (fun _ _ => sum_comm))
  rw [perm]
  apply sum_le_sum
  intro c _
  calc
    _ ≤ ∑ e, s * ((P (j-1)) b e * (P (k+1-j)) e c * (P k) b c) := by
      apply sum_le_sum
      intro e _
      have hh := mass17 M hM hsym r hr s hmass (k-1) b e c
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hh
        (mul_nonneg (mul_nonneg (hn _ _ _) (hn _ _ _)) (hn _ _ _)))
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      dsimp [f, P]
      by_cases hr' : r a e
      · simp only [hr', if_true]
        ring
      · simp [hr']
    _ = s * ((P k) b c * (P k) b c) := by
      rw [← mul_sum, ← sum_mul]
      have hp : (∑ e, (P (j-1)) b e * (P (k+1-j)) e c) = (P k) b c := by
        change ((M^(j-1)) * (M^(k+1-j))) b c = _
        rw [← pow_add, show j-1 + (k+1-j) = k by omega]
      rw [hp]
    _ = _ := by
      exact congrArg (fun z => s * ((P k) b c * z)) (symm17 M hsym k b c)

private theorem cwNonneg17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    {N : ℕ} (x : Fin N → W) : 0 ≤ cycW M x :=
  prod_nonneg (fun _ _ => hM _ _)

private theorem support17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u)
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (2*k) → W) (hx : cycW M x ≠ 0) :
    (M^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 ∧
    (M^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 := by
  classical
  let P := fun n : ℕ => M^n
  let bad := fun a b c : W => if (P (k-1)) a c = 0 ∨ (P k) b c = 0 then (1:ℝ) else 0
  let term := fun y : Fin (2*k) → W => cycW M y * bad (y ⟨0,by omega⟩) (y ⟨1,by omega⟩)
    (y ⟨k+1,by omega⟩)
  have hzero : ∑ y, term y = 0 := by
    dsimp only [term]
    rw [trip17 M k hk bad]
    apply sum_eq_zero
    intro a _
    apply sum_eq_zero
    intro b _
    apply sum_eq_zero
    intro c _
    by_cases ha : (P (k-1)) a c = 0
    · have hc : (P (k-1)) c a = 0 := (symm17 M hsym (k-1) c a).trans ha
      change _ * (P (k-1)) c a * _ = 0
      simp [hc]
    · by_cases hb : (P k) b c = 0
      · change _ * (P k) b c * _ * _ = 0
        simp [hb]
      · simp [bad, ha, hb]
  have hn (y) (_ : y ∈ univ) : 0 ≤ term y := by
    dsimp only [term,bad]
    exact mul_nonneg (cwNonneg17 M hM y) (by split <;> norm_num)
  have hh := (sum_eq_zero_iff_of_nonneg hn).mp hzero x (mem_univ x)
  dsimp only [term,bad] at hh
  by_contra! h
  have h' : (P (k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) = 0 ∨
      (P k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) = 0 := by tauto
  rw [if_pos h', mul_one] at hh
  exact hx hh

private theorem cs17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u)
    (R : ℝ) (hrow : ∀ a, ∑ b, M a b ≤ R) (k : ℕ) (hk : 2 ≤ k)
    (hit : (Fin (2*k) → W) → Prop) (C : ℝ)
    (hsecond : ∑ x : Fin (2*k) → W, (if hit x then cycW M x else 0) *
      ((M^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       (M^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩)) ≤ C) :
    (∑ x, if hit x then cycW M x else 0) ≤
      Real.sqrt ((R * trace (M ^ (2*(k-1)))) * C) := by
  classical
  let X := Fin (2*k) → W
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let T := fun x : X => if hit x then cycW M x else 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg hM
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  have hT (x : X) : 0 ≤ T x := by
    dsimp only [T]
    split
    · exact cwNonneg17 M hM x
    · rfl
  have hf (x : X) : 0 ≤ T x * (A x / B x) := mul_nonneg (hT x) (div_nonneg (hA x) (hB x))
  have hg (x : X) : 0 ≤ T x * (B x / A x) := mul_nonneg (hT x) (div_nonneg (hB x) (hA x))
  have cs := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset X)
    (fun x _ => hf x) (fun x _ => hg x) (r := T) (by
      intro x _
      by_cases h : cycW M x = 0
      · simp [T,h]
      · obtain ⟨h₁,h₂⟩ := support17 M hM hsym k hk x h
        have h₁' : A x ≠ 0 := h₁
        have h₂' : B x ≠ 0 := h₂
        apply le_of_eq
        field_simp [h₁',h₂'])
  have hfirst : ∑ x, T x * (A x / B x) ≤ R * trace (P (2*(k-1))) := by
    apply le_trans _ (upperFirst17 M hM R hrow k hk)
    apply sum_le_sum
    intro x _
    change T x * (A x / B x) ≤ cycW M x * (A x / B x)
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (hA x) (hB x))
    dsimp only [T]
    split
    · rfl
    · exact cwNonneg17 M hM x
  apply Real.le_sqrt_of_sq_le
  change (∑ x, T x)^2 ≤ _
  exact cs.trans (mul_le_mul hfirst hsecond (sum_nonneg (fun x _ => hg x))
    (le_trans (sum_nonneg (fun x _ => hf x)) hfirst))

private theorem traceSplit17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (a b : ℕ) :
    trace (M ^ (a + b)) = ∑ p : W × W, (M ^ a) p.1 p.2 * (M ^ b) p.2 p.1 := by
  simp [pow_add, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Log-convexité des traces paires. -/
private theorem logConvex17 {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (j : ℕ) (hj : 1 ≤ j) :
    trace (M ^ (2 * j)) ^ 2 ≤ trace (M ^ (2 * (j - 1))) * trace (M ^ (2 * (j + 1))) := by
  have hn := Matrix.pow_apply_nonneg hM
  let a := j - 1
  let b := j + 1
  rw [show 2 * j = a + b by dsimp [a, b]; omega, traceSplit17,
      show 2 * (j - 1) = a + a by dsimp [a]; omega, traceSplit17,
      show 2 * (j + 1) = b + b by dsimp [b]; omega, traceSplit17]
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun _ _ ↦ mul_nonneg (hn ..) (hn ..)
  · exact fun _ _ ↦ mul_nonneg (hn ..) (hn ..)
  · rintro ⟨u, v⟩ _
    dsimp only
    rw [symm17 M hsym a v u, symm17 M hsym b v u]
    exact le_of_eq (by ring)

-- Recopié de la preuve fusionnée de Sidorenko pour les cycles pairs (PR #641), vecteur test
-- unitaire quelconque.
private theorem symTrace17 {N k : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (v : Fin N → ℝ) (hvv : v ⬝ᵥ v = 1) :
    (v ⬝ᵥ (A.mulVec v)) ^ (2 * k) ≤ (A ^ (2 * k)).trace := by
  let U := hA.eigenvectorUnitary
  let ev : Fin N → ℝ := hA.eigenvalues
  have hspec : A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal ev *
      star (U : Matrix (Fin N) (Fin N) ℝ) := by
    have h := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, U, ev] using h
  have hpow : A ^ (2 * k) =
      Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal (fun i => ev i ^ (2 * k))) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow, Matrix.diagonal_pow]
    rfl
  have htr : (A ^ (2 * k)).trace = ∑ i : Fin N, ev i ^ (2 * k) := by
    rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    have hUU : star (U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [hUU, one_mul, Matrix.trace_diagonal]
  let w : Fin N → ℝ := (star (U : Matrix (Fin N) (Fin N) ℝ)).mulVec v
  have hstar_tr : star (U : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.transpose (U : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hww : ∑ i : Fin N, w i ^ 2 = 1 := by
    have hdot : w ⬝ᵥ w = 1 := by
      dsimp only [w]
      rw [Matrix.dotProduct_mulVec, hstar_tr, Matrix.vecMul_transpose,
        ← hstar_tr, Matrix.mulVec_mulVec]
      have hUU : (U : Matrix (Fin N) (Fin N) ℝ) * star (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
        Unitary.coe_mul_star_self U
      rw [hUU, Matrix.one_mulVec, hvv]
    simpa [dotProduct, sq] using hdot
  have hquad_rhs : v ⬝ᵥ (A.mulVec v) = ∑ i : Fin N, w i ^ 2 * ev i := by
    rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    have hvU : Matrix.vecMul v (U : Matrix (Fin N) (Fin N) ℝ) = w := by
      dsimp only [w]
      rw [hstar_tr, Matrix.mulVec_transpose]
    rw [hvU]
    change w ⬝ᵥ ((Matrix.diagonal ev).mulVec w) = _
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * k)) :=
    (even_two_mul k).convexOn_pow
  have hjensen := hconv.map_sum_le (t := Finset.univ) (w := fun i => w i ^ 2) (p := ev)
    (fun i _ => sq_nonneg (w i)) hww (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjensen
  have hle_tr : ∑ i : Fin N, w i ^ 2 * ev i ^ (2 * k) ≤ ∑ i : Fin N, ev i ^ (2 * k) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hw_le : w i ^ 2 ≤ 1 := by
      rw [← hww]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
    have hev_nn : 0 ≤ ev i ^ (2 * k) := (even_two_mul k).pow_nonneg (ev i)
    nlinarith
  rw [hquad_rhs, htr]
  exact le_trans hjensen hle_tr

/- ## À prouver -/

/-- Cycles homomorphes pondérés en conflit depuis la position 0 : version matrice de
`conflictA_le`. `R` borne les sommes de lignes, `s` la masse `∑_a [r e a] M b a`. -/
theorem conflictM_le {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (r : W → W → Prop) (hr : ∀ u w, r u w → r w u)
    (s R : ℝ) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hmass : ∀ b e, ∑ a, (if r e a then M b a else 0) ≤ s)
    (hrow : ∀ a, ∑ b, M a b ≤ R) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ j : Fin (2 * k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (x ⟨0, by omega⟩) (x j)
          then cycW M x else 0) ≤
      Real.sqrt (k * s * R * trace (M ^ (2 * (k - 1))) * trace (M ^ (2 * k))) := by
  classical
  have _hsR := mul_nonneg hs hR
  let X := Fin (2*k) → W
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let hit := fun x : X =>
    ∃ j : Fin (2*k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (a x) (x j)
  let T := fun x : X => @ite ℝ (hit x) (Classical.propDecidable _) (cycW M x) 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg hM
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  let idx := fun p : Fin k => (⟨p.val+1,by omega⟩ : Fin (2*k))
  let term := fun (x : X) (p : Fin k) =>
    cycW M x * (if r (a x) (x (idx p)) then B x / A x else 0)
  have hterm (x p) : 0 ≤ term x p := by
    apply mul_nonneg (cwNonneg17 M hM x)
    split
    · exact div_nonneg (hB x) (hA x)
    · rfl
  have hsecond : ∑ x, T x * (B x / A x) ≤ (k:ℝ) * (s * trace (P (2*k))) := by
    calc
      _ ≤ ∑ x, ∑ p, term x p := by
        apply sum_le_sum
        intro x _
        by_cases h : hit x
        · obtain ⟨j,hj,hjk,hrj⟩ := h
          let p : Fin k := ⟨j.val-1,by omega⟩
          have he : idx p = j := by apply Fin.ext; dsimp [idx,p]; omega
          calc
            _ = term x p := by
              have h' : hit x := ⟨j,hj,hjk,hrj⟩
              simp only [T,term,if_pos h',he,if_pos hrj]
            _ ≤ _ := single_le_sum (fun q _ => hterm x q) (mem_univ p)
        · simpa [T,h] using sum_nonneg (fun p (_ : p ∈ univ) => hterm x p)
      _ = ∑ p, ∑ x, term x p := sum_comm
      _ ≤ ∑ _p : Fin k, s * trace (P (2*k)) := by
        apply sum_le_sum
        intro p _
        exact upperOne17 M hM hsym r hr s hmass k (p.val+1) hk (by omega) (by omega)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ = ∑ x : X, T x := by
      apply sum_congr rfl
      intro x _
      by_cases h : hit x <;> simp only [T, hit, a] at h ⊢ <;> simp [h]
    _ ≤ _ := cs17 M hM hsym R hrow k hk hit ((k:ℝ) * (s * trace (M ^ (2*k)))) hsecond
    _ = _ := congrArg Real.sqrt (by ring)

/-- Sidorenko pour les cycles pairs, matrice symétrique portée par `S × S` : vecteur test
`1_S / √|S|` au lieu de `1 / √N`. -/
theorem sidorenko_supp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ u v, M u v = M v u)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hsupp : ∀ u v, M u v ≠ 0 → u ∈ S ∧ v ∈ S)
    (m : ℕ) :
    ((∑ a, ∑ b, M a b) / (#S : ℝ)) ^ (2 * m) ≤ trace (M ^ (2 * m)) := by
  have hSpos : (0:ℝ) < #S := by exact_mod_cast hS.card_pos
  have hA : M.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext a b
    exact hsym b a
  have hsq : Real.sqrt (#S : ℝ) ^ 2 = #S := Real.sq_sqrt hSpos.le
  have hsq_ne : Real.sqrt (#S : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hSpos).ne'
  let v : Fin n → ℝ := fun a => if a ∈ S then 1 / Real.sqrt (#S : ℝ) else 0
  have hvv : v ⬝ᵥ v = 1 := by
    have hterm (a : Fin n) : v a * v a = if a ∈ S then 1 / (#S : ℝ) else 0 := by
      by_cases ha : a ∈ S
      · simp only [v, if_pos ha]
        field_simp
        rw [hsq]
      · simp [v, ha]
    simp only [dotProduct, hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    field_simp
  have hquad : v ⬝ᵥ (M.mulVec v) = (∑ a, ∑ b, M a b) / (#S : ℝ) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : M a b = 0
    · simp [h]
    · obtain ⟨ha, hb⟩ := hsupp a b h
      simp only [v, if_pos ha, if_pos hb]
      field_simp
      rw [hsq]
  have h := symTrace17 (k := m) M hA v hvv
  rwa [hquad] at h

/-- Les traces paires d'une matrice symétrique positive non nulle sont strictement positives. -/
theorem trace_pos_M {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (hpos : ∃ u v, 0 < M u v) (k : ℕ) :
    0 < trace (M ^ (2 * k)) := by
  obtain ⟨u, v, huv⟩ := hpos
  have hn := Matrix.pow_apply_nonneg hM
  have h₂ : 0 < (M ^ 2) u u := by
    rw [sq, Matrix.mul_apply]
    calc
      0 < M u v * M v u := by rw [← hsym u v]; exact mul_pos huv huv
      _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (hM u z) (hM z u)) (mem_univ v)
  have hdiag : 0 < (M ^ (2 * k)) u u := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, Matrix.mul_apply]
      calc
        0 < (M ^ (2 * k)) u u * (M ^ 2) u u := mul_pos ih h₂
        _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (hn _ u z) (hn 2 z u)) (mem_univ u)
  exact hdiag.trans_le (single_le_sum (fun z _ => hn (2 * k) z z) (mem_univ u))

/-- Log-convexité des traces paires, avec `T_0 = |W|` : version matrice de
`trace_adjR_interp`. -/
theorem trace_interp_M {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (hsym : ∀ u v, M u v = M v u) (hpos : ∃ u v, 0 < M u v) (k : ℕ) (hk : 1 ≤ k) :
    trace (M ^ (2 * (k - 1))) ≤
      (Fintype.card W : ℝ) ^ (1 / (k : ℝ)) * trace (M ^ (2 * k)) ^ (1 - 1 / (k : ℝ)) := by
  let T (n : ℕ) := trace (M ^ (2 * n))
  have pos (n : ℕ) : 0 < T n := trace_pos_M M hM hsym hpos n
  let a (n : ℕ) := Real.log (T n)
  have step (n : ℕ) : a (n + 1) - a n ≤ a (n + 2) - a (n + 1) := by
    have h : T (n + 1) ^ 2 ≤ T n * T (n + 2) := by
      simpa [T] using logConvex17 M hM hsym (n + 1) (by omega)
    have h' := Real.log_le_log (sq_pos_of_pos (pos _)) h
    rw [Real.log_pow, Real.log_mul (pos _).ne' (pos _).ne'] at h'
    dsimp [a]; norm_num at h'; linarith
  have bound (n : ℕ) : a n - a 0 ≤ (n : ℝ) * (a (n + 1) - a n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      linarith [mul_le_mul_of_nonneg_left (step n) (Nat.cast_nonneg (α := ℝ) n), step n]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hc : T 0 = Fintype.card W := by simp [T]
  rw [← hc]
  change T (n + 1 - 1) ≤ T 0 ^ (1 / ((n + 1 : ℕ) : ℝ)) * T (n + 1) ^ (1 - 1 / ((n + 1 : ℕ) : ℝ))
  rw [Nat.add_sub_cancel]
  apply (Real.log_le_log_iff (pos _) (mul_pos (Real.rpow_pos_of_pos (pos _) _)
    (Real.rpow_pos_of_pos (pos _) _))).mp
  rw [Real.log_mul (Real.rpow_pos_of_pos (pos _) _).ne' (Real.rpow_pos_of_pos (pos _) _).ne',
    Real.log_rpow (pos _), Real.log_rpow (pos _)]
  change a n ≤ 1 / ((n + 1 : ℕ) : ℝ) * a 0 + (1 - 1 / ((n + 1 : ℕ) : ℝ)) * a (n + 1)
  push_cast
  field_simp
  linarith [bound n]

/- ## Lemme 18 : auxiliaires -/

/-- Tiroirs : une fibre porte au moins la part moyenne. -/
theorem pigeon18 {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty) :
    ∃ y ∈ t, #s ≤ #t * #(s.filter fun a => f a = y) := by
  obtain ⟨y, hy, hmax⟩ := t.exists_max_image (fun y => #(s.filter fun a => f a = y)) ht
  refine ⟨y, hy, ?_⟩
  rw [card_eq_sum_card_fiberwise (by intro a ha; exact hf a ha)]
  calc _ ≤ ∑ _b ∈ t, #(s.filter fun a => f a = y) := sum_le_sum hmax
    _ = _ := by rw [sum_const, smul_eq_mul]

/-- Un ensemble de triplets stable par `(x, y, z) ↦ (z, y, x)` a des multiplicités symétriques. -/
theorem swapCard18 {α : Type*} [DecidableEq α] (D : Finset (α × α × α))
    (hD : ∀ p ∈ D, (p.2.2, p.2.1, p.1) ∈ D) (a b : α) :
    #(D.filter fun q => q.1 = a ∧ q.2.2 = b) ≤ #(D.filter fun q => q.1 = b ∧ q.2.2 = a) := by
  apply card_le_card_of_injOn (fun q => (q.2.2, q.2.1, q.1))
  · intro q hq
    obtain ⟨hqD, h1, h2⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hD q hqD, h2, h1⟩
  · rintro ⟨x, y, z⟩ _ ⟨x', y', z'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

/- ## Lemme 18 : choix de `v`, `s`, `s'` et de l'ensemble de triplets `D` (étapes A et B) -/

/-- Lemme 2.17 de l'article sans symétrisation, puis une classe dyadique des multiplicités
`h(x,z) = hmat D x z`. `Δ` borne les degrés, `U` le nombre de 4-cycles étiquetés par arête. -/
theorem stepAB {n : ℕ} (G : SimpleGraph (Fin n)) (Δ U : ℝ)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ)
    (hU : ∀ e ∈ G.edgeFinset,
      (#(((univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2).filter fun t =>
          e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨ e = s(t.2.2.1, t.2.2.2) ∨
            e = s(t.2.2.2, t.1)) : ℝ) ≤ U)
    (hQ : 0 < #((univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2)) :
    ∃ (v : Fin n) (s s' : ℝ) (D : Finset (Fin n × Fin n × Fin n)),
      0 < s ∧ s ≤ 2 * Δ ∧ 0 < s' ∧
      (#((univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun t =>
          G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
            t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2) : ℝ) ≤
        2 * n * ((Nat.log 2 n : ℝ) + 1) ^ 2 * #D ∧
      (∀ t ∈ D, G.Adj v t.1 ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧
        (#(G.neighborFinset v ∩ G.neighborFinset t.2.1) : ℝ) ≤ s ∧
        (#(G.neighborFinset t.1 ∩ G.neighborFinset t.2.2) : ℝ) ≤ s) ∧
      (∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) ∧
      (∀ t ∈ D, s' ≤ hmat D t.1 t.2.2) ∧
      (#D : ℝ) ≤ 2 * s' * Δ ^ 2 ∧
      (∀ a b, hmat D a b ≤ s) ∧
      (∀ a, (#(rowSet D a) : ℝ) ≤ U) ∧
      (∀ a, (#(extSet D a) : ℝ) * s ≤ 4 * U) := by
  classical
  set c4 : Finset (Fin n × Fin n × Fin n × Fin n) :=
    (univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun t =>
      G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧ G.Adj t.2.2.2 t.1 ∧
        t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 with hc4
  have mem4 : ∀ t, t ∈ c4 ↔ (G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2.1 ∧ G.Adj t.2.2.1 t.2.2.2 ∧
      G.Adj t.2.2.2 t.1 ∧ t.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2) := fun t => by
    rw [hc4, mem_filter]; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin n → Fin n → ℕ,
      ∀ a b, d a b = #(G.neighborFinset a ∩ G.neighborFinset b) := ⟨_, fun _ _ => rfl⟩
  have dsymm : ∀ a b, d a b = d b a := fun a b => by rw [hd, hd, inter_comm]
  have ddeg : ∀ a b, d a b ≤ G.degree a := fun a b => by
    rw [hd, ← card_neighborFinset_eq_degree]; exact card_le_card inter_subset_left
  have dn : ∀ a b, d a b ≤ n := fun a b => by
    rw [hd]; exact (card_le_univ _).trans (by rw [Fintype.card_fin])
  obtain ⟨t0, ht0⟩ := card_pos.mp hQ
  have hU0 : 0 ≤ U :=
    le_trans (Nat.cast_nonneg _) (hU _ (G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr ((mem4 t0).mp ht0).1)))
  -- Étape 1 : la rotation `(a,b,c,d) ↦ (b,c,d,a)`.
  obtain ⟨c4', hc4', h1⟩ : ∃ c4' : Finset (Fin n × Fin n × Fin n × Fin n),
      (∀ t, t ∈ c4' ↔ t ∈ c4 ∧ d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1) ∧ #c4 ≤ 2 * #c4' := by
    refine ⟨c4.filter fun t => d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1, fun t => mem_filter, ?_⟩
    have hsplit := card_filter_add_card_filter_not (s := c4)
      (fun t => d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1)
    have hrot : #(c4.filter fun t => ¬ d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1) ≤
        #(c4.filter fun t => d t.2.1 t.2.2.2 ≤ d t.1 t.2.2.1) := by
      apply card_le_card_of_injOn (fun t => (t.2.1, t.2.2.1, t.2.2.2, t.1))
      · intro t ht
        obtain ⟨htc, hlt⟩ := mem_filter.mp ht
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (mem4 t).mp htc
        refine mem_filter.mpr ⟨(mem4 _).mpr ⟨h2, h3, h4, h1, h6, fun h => h5 h.symm⟩, ?_⟩
        show d t.2.2.1 t.1 ≤ d t.2.1 t.2.2.2
        rw [dsymm t.2.2.1 t.1]
        omega
      · rintro ⟨a, b, c, e⟩ _ ⟨a', b', c', e'⟩ _ h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        rfl
    omega
  -- Étape 2 : tiroirs sur `v = t.1`.
  have hn0 : (univ : Finset (Fin n)).Nonempty := ⟨t0.1, mem_univ _⟩
  obtain ⟨v, -, hv⟩ : ∃ v ∈ (univ : Finset (Fin n)),
      #c4' ≤ #(univ : Finset (Fin n)) * #(c4'.filter fun t => t.1 = v) :=
    pigeon18 c4' univ (fun t => t.1) (fun _ _ => mem_univ _) hn0
  rw [card_univ, Fintype.card_fin] at hv
  -- Étape 3 : tiroirs sur `j = Nat.log 2 (d v y)`.
  obtain ⟨j, -, hj⟩ : ∃ j ∈ range (Nat.log 2 n + 1),
      #(c4'.filter fun t => t.1 = v) ≤ #(range (Nat.log 2 n + 1)) *
        #((c4'.filter fun t => t.1 = v).filter fun t => Nat.log 2 (d v t.2.2.1) = j) := by
    refine pigeon18 (c4'.filter fun t => t.1 = v) (range (Nat.log 2 n + 1))
      (fun t => Nat.log 2 (d v t.2.2.1))
      (fun t _ => ?_) nonempty_range_add_one
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (dn _ _)))
  rw [card_range] at hj
  obtain ⟨D₀, hD₀, hAD⟩ : ∃ D₀ : Finset (Fin n × Fin n × Fin n),
      (∀ p, p ∈ D₀ ↔ (G.Adj v p.1 ∧ G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧ G.Adj p.2.2 v ∧
        v ≠ p.2.1 ∧ p.1 ≠ p.2.2) ∧ d p.1 p.2.2 ≤ d v p.2.1 ∧ Nat.log 2 (d v p.2.1) = j) ∧
      #((c4'.filter fun t => t.1 = v).filter fun t => Nat.log 2 (d v t.2.2.1) = j) ≤ #D₀ := by
    refine ⟨univ.filter fun p => (G.Adj v p.1 ∧ G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧
        G.Adj p.2.2 v ∧ v ≠ p.2.1 ∧ p.1 ≠ p.2.2) ∧ d p.1 p.2.2 ≤ d v p.2.1 ∧
        Nat.log 2 (d v p.2.1) = j,
      fun p => by rw [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩, ?_⟩
    apply card_le_card_of_injOn (fun t => t.2)
    · intro t ht
      obtain ⟨htA, hlog⟩ := mem_filter.mp ht
      obtain ⟨htc', ht1⟩ := mem_filter.mp htA
      obtain ⟨htc, hle⟩ := (hc4' t).mp htc'
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (mem4 t).mp htc
      rw [ht1] at h1 h4 h5 hle
      exact mem_filter.mpr ⟨mem_univ _, ⟨h1, h2, h3, h4, h5, h6⟩, hle, hlog⟩
    · intro t ht t' ht' h
      have e1 := (mem_filter.mp (mem_filter.mp ht).1).2
      have e2 := (mem_filter.mp (mem_filter.mp ht').1).2
      exact Prod.ext (e1.trans e2.symm) h
  -- Étape 4 : tiroirs sur `j' = Nat.log 2 (h(x,z))`.
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : Fin n → Fin n → ℕ,
      ∀ a b, h₀ a b = #(D₀.filter fun q => q.1 = a ∧ q.2.2 = b) := ⟨_, fun _ _ => rfl⟩
  have h0n : ∀ a b, h₀ a b ≤ n := by
    intro a b
    rw [hh₀]
    calc _ ≤ #(univ : Finset (Fin n)) := by
          apply card_le_card_of_injOn (fun q => q.2.1) (by intro q _; exact mem_univ _)
          intro q hq q' hq' h
          obtain ⟨-, hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨-, hq1', hq2'⟩ := mem_filter.mp hq'
          exact Prod.ext (hq1.trans hq1'.symm) (Prod.ext h (hq2.trans hq2'.symm))
      _ = n := by rw [card_univ, Fintype.card_fin]
  obtain ⟨j', -, hj'⟩ : ∃ j' ∈ range (Nat.log 2 n + 1), #D₀ ≤ #(range (Nat.log 2 n + 1)) *
      #(D₀.filter fun p => Nat.log 2 (h₀ p.1 p.2.2) = j') := by
    refine pigeon18 D₀ _ (fun p => Nat.log 2 (h₀ p.1 p.2.2)) (fun p _ => ?_) nonempty_range_add_one
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (h0n _ _)))
  rw [card_range] at hj'
  obtain ⟨D, hD, hDc⟩ : ∃ D : Finset (Fin n × Fin n × Fin n),
      (∀ p, p ∈ D ↔ p ∈ D₀ ∧ Nat.log 2 (h₀ p.1 p.2.2) = j') ∧
      #D₀ ≤ (Nat.log 2 n + 1) * #D := ⟨_, fun p => mem_filter, hj'⟩
  -- La borne de comptage.
  have hbig : #c4 ≤ 2 * n * (Nat.log 2 n + 1) ^ 2 * #D := by
    calc #c4 ≤ 2 * #c4' := h1
      _ ≤ 2 * (n * #(c4'.filter fun t => t.1 = v)) := Nat.mul_le_mul_left _ hv
      _ ≤ 2 * (n * ((Nat.log 2 n + 1) *
            #((c4'.filter fun t => t.1 = v).filter fun t => Nat.log 2 (d v t.2.2.1) = j))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hj)
      _ ≤ 2 * (n * ((Nat.log 2 n + 1) * #D₀)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hAD))
      _ ≤ 2 * (n * ((Nat.log 2 n + 1) * ((Nat.log 2 n + 1) * #D))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hDc))
      _ = 2 * n * (Nat.log 2 n + 1) ^ 2 * #D := by ring
  have hDpos : 0 < #D := by
    rcases Nat.eq_zero_or_pos #D with h | h
    · rw [h, mul_zero] at hbig; omega
    · exact h
  obtain ⟨t₀, ht₀⟩ := card_pos.mp hDpos
  -- Faits sur `D₀`, `h₀` et `D`.
  have hDsub : ∀ p ∈ D, p ∈ D₀ := fun p hp => ((hD p).mp hp).1
  have hD0f : ∀ p ∈ D₀, 2 ≤ d v p.2.1 ∧ 2 ^ j ≤ d v p.2.1 ∧ d v p.2.1 < 2 ^ (j + 1) ∧
      d p.1 p.2.2 < 2 ^ (j + 1) := by
    intro p hp
    obtain ⟨⟨h1, h2, h3, h4, -, h6⟩, hle, hlog⟩ := (hD₀ p).mp hp
    have h2le : 2 ≤ d v p.2.1 := by
      rw [hd, ← card_pair h6]
      apply card_le_card
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1,
          (G.mem_neighborFinset _ _).mpr h2.symm⟩
      · exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h4.symm,
          (G.mem_neighborFinset _ _).mpr h3⟩
    have hlo := Nat.pow_log_le_self 2 (show d v p.2.1 ≠ 0 by omega)
    have hhi := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (d v p.2.1)
    rw [hlog] at hlo hhi
    exact ⟨h2le, hlo, hhi, lt_of_le_of_lt hle hhi⟩
  have hD0sym : ∀ p ∈ D₀, (p.2.2, p.2.1, p.1) ∈ D₀ := by
    intro p hp
    obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle, hlog⟩ := (hD₀ p).mp hp
    exact (hD₀ _).mpr ⟨⟨h4.symm, h3.symm, h2.symm, h1.symm, h5, fun h => h6 h.symm⟩,
      (dsymm p.2.2 p.1).trans_le hle, hlog⟩
  have h0sym : ∀ a b, h₀ a b = h₀ b a := fun a b => by
    rw [hh₀, hh₀]
    exact le_antisymm (swapCard18 D₀ hD0sym a b) (swapCard18 D₀ hD0sym b a)
  have hfibD : ∀ p ∈ D, h₀ p.1 p.2.2 ≤ #(D.filter fun q => q.1 = p.1 ∧ q.2.2 = p.2.2) := by
    intro p hp
    rw [hh₀]
    apply card_le_card
    intro q hq
    obtain ⟨hqD, hq1, hq2⟩ := mem_filter.mp hq
    refine mem_filter.mpr ⟨(hD q).mpr ⟨hqD, ?_⟩, hq1, hq2⟩
    rw [hq1, hq2]; exact ((hD p).mp hp).2
  have hfibD' : ∀ a b, #(D.filter fun q => q.1 = a ∧ q.2.2 = b) ≤ h₀ a b := by
    intro a b
    rw [hh₀]
    apply card_le_card
    intro q hq
    obtain ⟨hqD, hq1, hq2⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hDsub q hqD, hq1, hq2⟩
  have hDcls : ∀ p ∈ D, 2 ^ j' ≤ h₀ p.1 p.2.2 ∧ h₀ p.1 p.2.2 < 2 ^ (j' + 1) := by
    intro p hp
    obtain ⟨hp0, hlog⟩ := (hD p).mp hp
    have hne : h₀ p.1 p.2.2 ≠ 0 := by
      rw [hh₀]; exact (card_pos.mpr ⟨p, mem_filter.mpr ⟨hp0, rfl, rfl⟩⟩).ne'
    have hlo := Nat.pow_log_le_self 2 hne
    have hhi := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (h₀ p.1 p.2.2)
    rw [hlog] at hlo hhi
    exact ⟨hlo, hhi⟩
  have hmatE : ∀ a b, hmat D a b = (#(D.filter fun q => q.1 = a ∧ q.2.2 = b) : ℝ) := by
    intro a b
    simp only [hmat]
    congr 2
    ext q
    simp only [mem_filter]
  have memR : ∀ a q, q ∈ rowSet D a ↔ q ∈ D ∧ q.1 = a := by
    intro a q
    simp only [rowSet, mem_filter]
  have memE : ∀ a y, y ∈ extSet D a ↔ ∃ q ∈ D, q.1 = a ∧ q.2.1 = y := by
    intro a y
    simp only [extSet, rowSet, mem_image, mem_filter, and_assoc]
  refine ⟨v, 2 ^ (j + 1), 2 ^ j', D, by positivity, ?_, by positivity, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- `s ≤ 2Δ`
    obtain ⟨-, hlo, -, -⟩ := hD0f t₀ (hDsub t₀ ht₀)
    have e1 : (2 : ℝ) ^ j ≤ d v t₀.2.1 := by exact_mod_cast hlo
    have e2 : (d v t₀.2.1 : ℝ) ≤ G.degree v := by exact_mod_cast ddeg _ _
    rw [pow_succ]
    linarith [hdeg v]
  · -- la borne de comptage
    exact_mod_cast hbig
  · -- adjacences et codegrés
    intro t ht
    obtain ⟨⟨h1, h2, h3, -, -, -⟩, -, -⟩ := (hD₀ t).mp (hDsub t ht)
    obtain ⟨-, -, hhi, hhi'⟩ := hD0f t (hDsub t ht)
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [← hd]; exact_mod_cast hhi.le
    · rw [← hd]; exact_mod_cast hhi'.le
  · -- symétrie
    intro t ht
    obtain ⟨ht0, hlog⟩ := (hD t).mp ht
    refine (hD _).mpr ⟨hD0sym t ht0, ?_⟩
    show Nat.log 2 (h₀ t.2.2 t.1) = j'
    rw [h0sym]; exact hlog
  · -- `s' ≤ hmat D t.1 t.2.2`
    intro t ht
    rw [hmatE]
    exact_mod_cast (hDcls t ht).1.trans (hfibD t ht)
  · -- `#D ≤ 2 s' Δ²`
    have hmaps : ∀ q ∈ D, (q.1, q.2.2) ∈ G.neighborFinset v ×ˢ G.neighborFinset v := by
      intro q hq
      obtain ⟨⟨h1, -, -, h4, -, -⟩, -, -⟩ := (hD₀ q).mp (hDsub q hq)
      exact mem_product.mpr ⟨(G.mem_neighborFinset _ _).mpr h1,
        (G.mem_neighborFinset _ _).mpr h4.symm⟩
    have hcard : #D ≤ #(G.neighborFinset v ×ˢ G.neighborFinset v) * 2 ^ (j' + 1) := by
      rw [card_eq_sum_card_fiberwise (f := fun q => (q.1, q.2.2))
        (by intro q hq; exact hmaps q hq)]
      refine (sum_le_card_nsmul _ _ _ ?_).trans (by rw [smul_eq_mul])
      rintro ⟨a, b⟩ -
      rcases (D.filter fun q => (q.1, q.2.2) = (a, b)).eq_empty_or_nonempty with he | ⟨p, hp⟩
      · rw [he, card_empty]; exact Nat.zero_le _
      · obtain ⟨hpD, hpab⟩ := mem_filter.mp hp
        simp only [Prod.mk.injEq] at hpab
        obtain ⟨rfl, rfl⟩ := hpab
        refine le_trans ?_ (hDcls p hpD).2.le
        refine le_trans ?_ (hfibD' p.1 p.2.2)
        apply card_le_card
        intro q hq
        obtain ⟨hqD, hq'⟩ := mem_filter.mp hq
        simp only [Prod.mk.injEq] at hq'
        exact mem_filter.mpr ⟨hqD, hq'⟩
    rw [card_product, card_neighborFinset_eq_degree] at hcard
    have hc : (#D : ℝ) ≤ (G.degree v : ℝ) * G.degree v * 2 ^ (j' + 1) := by
      exact_mod_cast hcard
    have hd0 : (0 : ℝ) ≤ G.degree v := Nat.cast_nonneg _
    have hdv := hdeg v
    have hsq : (G.degree v : ℝ) * G.degree v ≤ Δ ^ 2 := by nlinarith
    calc (#D : ℝ) ≤ (G.degree v : ℝ) * G.degree v * 2 ^ (j' + 1) := hc
      _ ≤ Δ ^ 2 * 2 ^ (j' + 1) := mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 2 * 2 ^ j' * Δ ^ 2 := by ring
  · -- `hmat D a b ≤ s`
    intro a b
    rw [hmatE]
    rcases (D.filter fun q => q.1 = a ∧ q.2.2 = b).eq_empty_or_nonempty with he | ⟨p, hp⟩
    · rw [he, card_empty, Nat.cast_zero]; positivity
    · obtain ⟨hpD, rfl, rfl⟩ := mem_filter.mp hp
      have hcd : #(D.filter fun q => q.1 = p.1 ∧ q.2.2 = p.2.2) ≤ d p.1 p.2.2 := by
        rw [hd]
        apply card_le_card_of_injOn (fun q => q.2.1)
        · intro q hq
          obtain ⟨hqD, hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨⟨-, h2, h3, -, -, -⟩, -, -⟩ := (hD₀ q).mp (hDsub q hqD)
          rw [← hq1, ← hq2]
          exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h2,
            (G.mem_neighborFinset _ _).mpr h3.symm⟩
        · intro q hq q' hq' h
          obtain ⟨-, hq1, hq2⟩ := mem_filter.mp hq
          obtain ⟨-, hq1', hq2'⟩ := mem_filter.mp hq'
          exact Prod.ext (hq1.trans hq1'.symm) (Prod.ext h (hq2.trans hq2'.symm))
      exact_mod_cast hcd.trans (hD0f p (hDsub p hpD)).2.2.2.le
  · -- `#(rowSet D a) ≤ U`
    intro a
    rcases (rowSet D a).eq_empty_or_nonempty with he | ⟨p, hp⟩
    · rw [he, card_empty, Nat.cast_zero]; exact hU0
    · obtain ⟨hpD, rfl⟩ := (memR a p).mp hp
      obtain ⟨⟨hva, -, -, -, -, -⟩, -, -⟩ := (hD₀ p).mp (hDsub p hpD)
      refine le_trans (Nat.cast_le.mpr (card_le_card_of_injOn
        (fun q => (v, q.1, q.2.1, q.2.2)) ?_ ?_)) (hU _ (G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hva)))
      · intro q hq
        obtain ⟨hqD, hq1⟩ := (memR _ q).mp hq
        obtain ⟨hc, -, -⟩ := (hD₀ q).mp (hDsub q hqD)
        refine mem_filter.mpr ⟨(mem4 _).mpr hc, Or.inl ?_⟩
        show s(v, p.1) = s(v, q.1)
        rw [hq1]
      · intro q _ q' _ h
        have e1 : q.1 = q'.1 := congrArg (fun t => t.2.1) h
        have e2 : q.2.1 = q'.2.1 := congrArg (fun t => t.2.2.1) h
        have e3 : q.2.2 = q'.2.2 := congrArg (fun t => t.2.2.2) h
        exact Prod.ext e1 (Prod.ext e2 e3)
  · -- `#(extSet D a) * s ≤ 4U`
    intro a
    rcases (extSet D a).eq_empty_or_nonempty with he | ⟨y₀, hy₀⟩
    · rw [he, card_empty, Nat.cast_zero, zero_mul]; linarith
    · obtain ⟨p, hpD, rfl, -⟩ := (memE a y₀).mp hy₀
      obtain ⟨⟨hva, -, -, -, -, -⟩, -, -⟩ := (hD₀ p).mp (hDsub p hpD)
      have hW : ∀ y ∈ extSet D p.1, (2 : ℝ) ^ (j + 1) / 4 ≤
          #((G.neighborFinset v ∩ G.neighborFinset y).erase p.1) := by
        intro y hy
        obtain ⟨q, hqD, hq1, rfl⟩ := (memE _ y).mp hy
        obtain ⟨⟨h1, h2, -, -, -, -⟩, -, -⟩ := (hD₀ q).mp (hDsub q hqD)
        obtain ⟨h2le, hlo, -, -⟩ := hD0f q (hDsub q hqD)
        have hmem : p.1 ∈ G.neighborFinset v ∩ G.neighborFinset q.2.1 := by
          rw [← hq1]
          exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1,
            (G.mem_neighborFinset _ _).mpr h2.symm⟩
        rw [cast_card_erase_of_mem hmem, ← hd]
        have e1 : (2 : ℝ) ^ j ≤ d v q.2.1 := by exact_mod_cast hlo
        have e2 : (2 : ℝ) ≤ d v q.2.1 := by exact_mod_cast h2le
        rw [pow_succ]
        linarith
      have hS : (#((extSet D p.1).sigma fun y =>
          (G.neighborFinset v ∩ G.neighborFinset y).erase p.1) : ℝ) ≤ U := by
        refine le_trans (Nat.cast_le.mpr (card_le_card_of_injOn
          (fun r : (Σ _ : Fin n, Fin n) => (v, p.1, r.1, r.2)) ?_ ?_))
          (hU _ (G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hva)))
        · rintro ⟨y, w⟩ hr
          obtain ⟨hy, hw⟩ := mem_sigma.mp hr
          obtain ⟨hwa, hw'⟩ := mem_erase.mp hw
          obtain ⟨hvw, hyw⟩ := mem_inter.mp hw'
          obtain ⟨q, hqD, hq1, rfl⟩ := (memE _ y).mp hy
          obtain ⟨⟨-, h2, -, -, h5, -⟩, -, -⟩ := (hD₀ q).mp (hDsub q hqD)
          refine mem_filter.mpr ⟨(mem4 _).mpr ⟨hva, ?_, (G.mem_neighborFinset _ _).mp hyw,
            ((G.mem_neighborFinset _ _).mp hvw).symm, h5, fun h => hwa h.symm⟩, Or.inl rfl⟩
          show G.Adj p.1 q.2.1
          rw [← hq1]; exact h2
        · rintro ⟨y, w⟩ _ ⟨y', w'⟩ _ h
          have e1 : y = y' := congrArg (fun t => t.2.2.1) h
          have e2 : w = w' := congrArg (fun t => t.2.2.2) h
          subst e1; subst e2; rfl
      have hsum : (#(extSet D p.1) : ℝ) * ((2 : ℝ) ^ (j + 1) / 4) ≤ U := by
        calc (#(extSet D p.1) : ℝ) * ((2 : ℝ) ^ (j + 1) / 4)
            = ∑ _y ∈ extSet D p.1, (2 : ℝ) ^ (j + 1) / 4 := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ ∑ y ∈ extSet D p.1,
              (#((G.neighborFinset v ∩ G.neighborFinset y).erase p.1) : ℝ) := sum_le_sum hW
          _ = (#((extSet D p.1).sigma fun y =>
              (G.neighborFinset v ∩ G.neighborFinset y).erase p.1) : ℝ) := by
              rw [card_sigma, Nat.cast_sum]
          _ ≤ U := hS
      calc (#(extSet D p.1) : ℝ) * 2 ^ (j + 1)
          = 4 * ((#(extSet D p.1) : ℝ) * ((2 : ℝ) ^ (j + 1) / 4)) := by ring
        _ ≤ 4 * U := by linarith

/- ## Lemme 19 : la matrice `hmat D` et le comptage des cycles (étape C) -/

theorem hmat_nonneg {W : Type} [Fintype W] (D : Finset (W × W × W)) (a b : W) :
    0 ≤ hmat D a b := by
  unfold hmat
  positivity

theorem hmat_symm {W : Type} [Fintype W] (D : Finset (W × W × W))
    (hsymm : ∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) (a b : W) :
    hmat D a b = hmat D b a := by
  unfold hmat
  congr 1
  apply Finset.card_nbij' (fun t => (t.2.2, t.2.1, t.1)) (fun t => (t.2.2, t.2.1, t.1))
  · intro t ht
    simp only [mem_coe, mem_filter] at ht ⊢
    exact ⟨hsymm t ht.1, ht.2.2, ht.2.1⟩
  · intro t ht
    simp only [mem_coe, mem_filter] at ht ⊢
    exact ⟨hsymm t ht.1, ht.2.2, ht.2.1⟩
  · intro t _
    rfl
  · intro t _
    rfl

private theorem hmat_row19 {W : Type} [Fintype W] (D : Finset (W × W × W)) (a : W) :
    ∑ b, hmat D a b = #(rowSet D a) := by
  unfold hmat rowSet
  rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := fun t => t.2.2) (t := univ)
    (fun _ _ => mem_univ _)]
  push_cast
  refine sum_congr rfl fun b _ => ?_
  rw [filter_filter]

theorem hmat_sum {W : Type} [Fintype W] (D : Finset (W × W × W)) :
    ∑ a, ∑ b, hmat D a b = #D := by
  rw [sum_congr rfl fun a _ => hmat_row19 D a, ← Nat.cast_sum,
    card_eq_sum_card_fiberwise (s := D) (f := fun t => t.1) (t := univ) (fun _ _ => mem_univ _)]
  rfl

theorem hmat_row {W : Type} [Fintype W] (D : Finset (W × W × W)) (a : W) :
    ∑ b, hmat D a b = #(rowSet D a) :=
  hmat_row19 D a

theorem hmat_supp {W : Type} [Fintype W] (D : Finset (W × W × W)) (S : Finset W)
    (hfirst : ∀ t ∈ D, t.1 ∈ S) (hsymm : ∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) (a b : W)
    (hab : hmat D a b ≠ 0) : a ∈ S ∧ b ∈ S := by
  unfold hmat at hab
  have hne : (D.filter fun t => t.1 = a ∧ t.2.2 = b).Nonempty := by
    rw [← card_pos]
    exact Nat.pos_of_ne_zero (by exact_mod_cast hab)
  obtain ⟨t, ht⟩ := hne
  rw [mem_filter] at ht
  obtain ⟨htD, rfl, rfl⟩ := ht
  exact ⟨hfirst t htD, hfirst _ (hsymm t htD)⟩

/-- `hmat D a b` compte les milieux `y` des triplets `(a, y, b)` de `D`. -/
private theorem hmat_eq_card19 {W : Type} [Fintype W] (D : Finset (W × W × W)) (a b : W) :
    hmat D a b = (#(univ.filter fun y => (a, y, b) ∈ D) : ℝ) := by
  unfold hmat
  congr 1
  apply Finset.card_nbij' (fun t => t.2.1) (fun y => (a, y, b))
  · intro t ht
    simp only [mem_coe, mem_filter, mem_univ, true_and] at ht ⊢
    obtain ⟨h, h1, h2⟩ := ht
    rw [← h1, ← h2]
    exact h
  · intro y hy
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hy
    simp [hy]
  · intro t ht
    simp only [mem_coe, mem_filter] at ht
    obtain ⟨_, h1, h2⟩ := ht
    rw [← h1, ← h2]
  · intro y _
    rfl

/-- Cardinal d'un ensemble de paires, fibre par fibre selon la première coordonnée. -/
private theorem card_prod19 {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (S : Finset (α × β)) :
    #S = ∑ a, #(univ.filter fun b => (a, b) ∈ S) := by
  calc #S = #(univ.filter fun p => p ∈ S) := by
        congr 1
        ext p
        simp
    _ = ∑ a, ∑ b, (if (a, b) ∈ S then 1 else 0) := by
        rw [card_filter, Fintype.sum_prod_type]
    _ = ∑ a, #(univ.filter fun b => (a, b) ∈ S) := by
        simp only [card_filter]

/-- À `x` fixé, les `y` admissibles forment un `piFinset` de cardinal `cycW (hmat D) x`. -/
private theorem fiber_card19 {W : Type} [Fintype W] (D : Finset (W × W × W)) {m : ℕ}
    (x : Fin m → W) :
    (#(univ.filter fun y : Fin m → W =>
        ∀ l : Fin m, (x l, y l, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D) : ℝ) =
      cycW (hmat D) x := by
  have h : (univ.filter fun y : Fin m → W =>
        ∀ l : Fin m, (x l, y l, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D) =
      Fintype.piFinset fun l : Fin m =>
        univ.filter fun c => (x l, c, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D := by
    ext y
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset, Nat.cast_prod]
  unfold cycW
  refine prod_congr rfl fun l _ => ?_
  rw [hmat_eq_card19]

/-- À `x` fixé, un ensemble de `y` admissibles où `y j` est déterminé par les autres
coordonnées a un cardinal au plus `cycW (hmat D) x / s'`. -/
private theorem fiber_bound19 {W : Type} [Fintype W] (D : Finset (W × W × W)) {m : ℕ}
    (s' : ℝ) (hs' : 0 < s') (hlow : ∀ t ∈ D, s' ≤ hmat D t.1 t.2.2)
    (x : Fin m → W) (j : Fin m) (A : Finset (Fin m → W))
    (hA : ∀ y ∈ A, ∀ l : Fin m, (x l, y l, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D)
    (hinj : ∀ y ∈ A, ∀ y' ∈ A, (∀ l, l ≠ j → y l = y' l) → y = y') :
    s' * (#A : ℝ) ≤ cycW (hmat D) x := by
  set Yf : Fin m → Finset W := fun l =>
    univ.filter fun c => (x l, c, x ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D with hYf
  have hcyc : cycW (hmat D) x = ∏ l, (#(Yf l) : ℝ) := by
    unfold cycW
    refine prod_congr rfl fun l _ => ?_
    rw [hmat_eq_card19]
  rcases A.eq_empty_or_nonempty with hE | ⟨y0, hy0⟩
  · rw [hE, card_empty, Nat.cast_zero, mul_zero, hcyc]
    exact prod_nonneg fun l _ => Nat.cast_nonneg _
  · have hMj : s' ≤ (#(Yf j) : ℝ) := by
      have := hlow _ (hA y0 hy0 j)
      rw [hmat_eq_card19] at this
      exact this
    have hcard : #A ≤ ∏ l ∈ univ.erase j, #(Yf l) := by
      calc #A ≤ #(Fintype.piFinset (Function.update Yf j {x j})) := by
            apply card_le_card_of_injOn (fun y => Function.update y j (x j))
            · intro y hy
              simp only [mem_coe, Fintype.mem_piFinset]
              intro l
              by_cases hl : l = j
              · subst hl
                simp
              · rw [Function.update_of_ne hl, Function.update_of_ne hl]
                simp only [hYf, mem_filter, mem_univ, true_and]
                exact hA y hy l
            · intro y hy y' hy' hyy
              apply hinj y hy y' hy'
              intro l hl
              have := congrFun hyy l
              simp only [Function.update_of_ne hl] at this
              exact this
        _ = ∏ l ∈ univ.erase j, #(Yf l) := by
            rw [Fintype.card_piFinset, ← mul_prod_erase univ _ (mem_univ j),
              Function.update_self, card_singleton, one_mul]
            refine prod_congr rfl fun l hl => ?_
            rw [Function.update_of_ne (ne_of_mem_erase hl)]
    have hP : 0 ≤ ∏ l ∈ univ.erase j, (#(Yf l) : ℝ) :=
      prod_nonneg fun l _ => Nat.cast_nonneg _
    calc s' * (#A : ℝ) ≤ s' * ∏ l ∈ univ.erase j, (#(Yf l) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hs'.le
          exact_mod_cast hcard
      _ ≤ (#(Yf j) : ℝ) * ∏ l ∈ univ.erase j, (#(Yf l) : ℝ) :=
          mul_le_mul_of_nonneg_right hMj hP
      _ = cycW (hmat D) x := by
          rw [hcyc, mul_prod_erase univ (fun l => (#(Yf l) : ℝ)) (mem_univ j)]

/-- Forme générale de `cycSet_card`, pour des cycles de longueur `2m` quelconque. -/
private theorem cycSet_card19 {W : Type} [Fintype W] (D : Finset (W × W × W)) (m : ℕ)
    (s' : ℝ) (hs' : 0 < s') (hlow : ∀ t ∈ D, s' ≤ hmat D t.1 t.2.2) :
    ∑ x : Fin m → W, cycW (hmat D) x -
        ∑ x : Fin m → W,
          (if ∃ i j : Fin m, i ≠ j ∧ x i = x j then cycW (hmat D) x else 0) -
        2 * (m : ℝ) ^ 2 * (∑ x : Fin m → W, cycW (hmat D) x) / s' ≤
      (#(cycSet D m) : ℝ) := by
  set T := ∑ x : Fin m → W, cycW (hmat D) x with hT
  -- L'entrelacement `x₀ y₀ x₁ y₁ ⋯`.
  let ι : (Fin m → W) × (Fin m → W) → Fin (2 * m) → W := fun p q =>
    if q.val % 2 = 0 then p.1 ⟨q.val / 2, by have := q.isLt; omega⟩
    else p.2 ⟨q.val / 2, by have := q.isLt; omega⟩
  have hιe : ∀ p (q : Fin (2 * m)) (i : Fin m), q.val = 2 * i.val → ι p q = p.1 i := by
    intro p q i hq
    simp only [ι]
    rw [if_pos (by omega)]
    exact congrArg p.1 (Fin.ext (by show q.val / 2 = i.val; omega))
  have hιo : ∀ p (q : Fin (2 * m)) (i : Fin m), q.val = 2 * i.val + 1 → ι p q = p.2 i := by
    intro p q i hq
    simp only [ι]
    rw [if_neg (by omega)]
    exact congrArg p.2 (Fin.ext (by show q.val / 2 = i.val; omega))
  have hmod : ∀ i : Fin m, (2 * i.val + 2) % (2 * m) = 2 * ((i.val + 1) % m) := by
    intro i
    rw [show 2 * i.val + 2 = 2 * (i.val + 1) by ring, Nat.mul_mod_mul_left]
  -- Les paires admissibles et leurs sous-ensembles.
  set V := univ.filter fun p : (Fin m → W) × (Fin m → W) =>
    ∀ l : Fin m, (p.1 l, p.2 l, p.1 ⟨(l.val + 1) % m, Nat.mod_lt _ l.pos⟩) ∈ D with hV
  set G := V.filter fun p => Function.Injective (ι p) with hG
  set BT := V.filter fun p => ∃ i j : Fin m, i ≠ j ∧ p.1 i = p.1 j with hBT
  set BY := (univ : Finset (Fin m × Fin m)).biUnion
    (fun ij => V.filter fun p => ij.1 ≠ ij.2 ∧ p.2 ij.1 = p.2 ij.2) with hBY
  set BX := (univ : Finset (Fin m × Fin m)).biUnion
    (fun ij => V.filter fun p => p.1 ij.1 = p.2 ij.2) with hBX
  -- `#V = T`.
  have hVc : (#V : ℝ) = T := by
    rw [card_prod19 V, Nat.cast_sum, hT]
    refine sum_congr rfl fun x _ => ?_
    rw [← fiber_card19 D x]
    congr 2
    ext y
    simp [hV]
  -- `#BT` : le terme des `x` répétés.
  have hBTc : (#BT : ℝ) = ∑ x : Fin m → W,
      (if ∃ i j : Fin m, i ≠ j ∧ x i = x j then cycW (hmat D) x else 0) := by
    rw [card_prod19 BT, Nat.cast_sum]
    refine sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [← fiber_card19 D x]
      congr 2
      ext y
      simp [hBT, hV, h]
    · rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
      intro y _ hy
      simp only [hBT, mem_filter] at hy
      exact h hy.2
  -- Chaque paire de positions (YY) ou (TY) coûte au plus `T / s'`.
  have hYc : ∀ ij : Fin m × Fin m,
      (#(V.filter fun p => ij.1 ≠ ij.2 ∧ p.2 ij.1 = p.2 ij.2) : ℝ) ≤ T / s' := by
    intro ij
    rw [le_div_iff₀ hs', mul_comm, card_prod19, Nat.cast_sum, mul_sum, hT]
    refine sum_le_sum fun x _ => ?_
    apply fiber_bound19 D s' hs' hlow x ij.2
    · intro y hy
      simp only [hV, mem_filter, mem_univ, true_and] at hy
      exact hy.1
    · intro y hy y' hy' hyy
      simp only [hV, mem_filter, mem_univ, true_and] at hy hy'
      funext l
      by_cases hl : l = ij.2
      · rw [hl, ← hy.2.2, ← hy'.2.2]
        exact hyy ij.1 hy.2.1
      · exact hyy l hl
  have hXc : ∀ ij : Fin m × Fin m,
      (#(V.filter fun p => p.1 ij.1 = p.2 ij.2) : ℝ) ≤ T / s' := by
    intro ij
    rw [le_div_iff₀ hs', mul_comm, card_prod19, Nat.cast_sum, mul_sum, hT]
    refine sum_le_sum fun x _ => ?_
    apply fiber_bound19 D s' hs' hlow x ij.2
    · intro y hy
      simp only [hV, mem_filter, mem_univ, true_and] at hy
      exact hy.1
    · intro y hy y' hy' hyy
      simp only [hV, mem_filter, mem_univ, true_and] at hy hy'
      funext l
      by_cases hl : l = ij.2
      · rw [hl, ← hy.2, ← hy'.2]
      · exact hyy l hl
  have hpairs : ((Fintype.card (Fin m × Fin m) : ℕ) : ℝ) = (m : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hBYc : (#BY : ℝ) ≤ (m : ℝ) ^ 2 * (T / s') := by
    calc (#BY : ℝ) ≤ ∑ ij : Fin m × Fin m,
          (#(V.filter fun p => ij.1 ≠ ij.2 ∧ p.2 ij.1 = p.2 ij.2) : ℝ) := by
          rw [hBY]
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _ij : Fin m × Fin m, T / s' := sum_le_sum fun ij _ => hYc ij
      _ = (m : ℝ) ^ 2 * (T / s') := by
          rw [sum_const, card_univ, nsmul_eq_mul, hpairs]
  have hBXc : (#BX : ℝ) ≤ (m : ℝ) ^ 2 * (T / s') := by
    calc (#BX : ℝ) ≤ ∑ ij : Fin m × Fin m,
          (#(V.filter fun p => p.1 ij.1 = p.2 ij.2) : ℝ) := by
          rw [hBX]
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _ij : Fin m × Fin m, T / s' := sum_le_sum fun ij _ => hXc ij
      _ = (m : ℝ) ^ 2 * (T / s') := by
          rw [sum_const, card_univ, nsmul_eq_mul, hpairs]
  -- Les paires injectives donnent des cycles de `cycSet D m`.
  have hGc : #G ≤ #(cycSet D m) := by
    apply card_le_card_of_injOn ι
    · intro p hp
      simp only [hG, hV, mem_coe, mem_filter, mem_univ, true_and] at hp
      simp only [cycSet, mem_coe, mem_filter, mem_univ, true_and]
      refine ⟨hp.2, fun i => ?_⟩
      have e1 := hιe p ⟨2 * i.val, by have := i.isLt; omega⟩ i rfl
      have e2 := hιo p ⟨2 * i.val + 1, by have := i.isLt; omega⟩ i rfl
      have e3 := hιe p ⟨(2 * i.val + 2) % (2 * m), Nat.mod_lt _ (by have := i.isLt; omega)⟩
        ⟨(i.val + 1) % m, Nat.mod_lt _ i.pos⟩ (hmod i)
      rw [e1, e2, e3]
      exact hp.1 i
    · intro p _ p' _ hpp
      have h1 : ∀ i : Fin m, p.1 i = p'.1 i := fun i => by
        have := congrFun hpp ⟨2 * i.val, by have := i.isLt; omega⟩
        rwa [hιe p _ i rfl, hιe p' _ i rfl] at this
      have h2 : ∀ i : Fin m, p.2 i = p'.2 i := fun i => by
        have := congrFun hpp ⟨2 * i.val + 1, by have := i.isLt; omega⟩
        rwa [hιo p _ i rfl, hιo p' _ i rfl] at this
      exact Prod.ext (funext h1) (funext h2)
  -- Toute paire admissible est injective ou mauvaise.
  have hcover : V ⊆ G ∪ (BT ∪ (BY ∪ BX)) := by
    intro p hp
    by_cases hinj : Function.Injective (ι p)
    · exact mem_union_left _ (by rw [hG, mem_filter]; exact ⟨hp, hinj⟩)
    · apply mem_union_right
      obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hinj
      simp only [ι] at hab
      have ha2 : a.val / 2 < m := by have := a.isLt; omega
      have hb2 : b.val / 2 < m := by have := b.isLt; omega
      split_ifs at hab with ha hb hb
      · refine mem_union_left _ ?_
        rw [hBT, mem_filter]
        refine ⟨hp, ⟨a.val / 2, ha2⟩, ⟨b.val / 2, hb2⟩, ?_, hab⟩
        intro h
        rw [Fin.mk.injEq] at h
        exact hne (Fin.ext (by omega))
      · refine mem_union_right _ (mem_union_right _ ?_)
        rw [hBX, mem_biUnion]
        exact ⟨(⟨a.val / 2, ha2⟩, ⟨b.val / 2, hb2⟩), mem_univ _, mem_filter.mpr ⟨hp, hab⟩⟩
      · refine mem_union_right _ (mem_union_right _ ?_)
        rw [hBX, mem_biUnion]
        exact ⟨(⟨b.val / 2, hb2⟩, ⟨a.val / 2, ha2⟩), mem_univ _, mem_filter.mpr ⟨hp, hab.symm⟩⟩
      · refine mem_union_right _ (mem_union_left _ ?_)
        rw [hBY, mem_biUnion]
        refine ⟨(⟨a.val / 2, ha2⟩, ⟨b.val / 2, hb2⟩), mem_univ _, mem_filter.mpr ⟨hp, ?_, hab⟩⟩
        intro h
        rw [Fin.mk.injEq] at h
        exact hne (Fin.ext (by omega))
  have hcard : #V ≤ #G + (#BT + (#BY + #BX)) := by
    calc #V ≤ #(G ∪ (BT ∪ (BY ∪ BX))) := card_le_card hcover
      _ ≤ #G + #(BT ∪ (BY ∪ BX)) := card_union_le _ _
      _ ≤ #G + (#BT + #(BY ∪ BX)) := by gcongr; exact card_union_le _ _
      _ ≤ #G + (#BT + (#BY + #BX)) := by gcongr; exact card_union_le _ _
  have hcardR : (#V : ℝ) ≤ #G + (#BT + (#BY + #BX)) := by exact_mod_cast hcard
  have hGR : (#G : ℝ) ≤ #(cycSet D m) := by exact_mod_cast hGc
  have hsplit : 2 * (m : ℝ) ^ 2 * T / s' = (m : ℝ) ^ 2 * (T / s') + (m : ℝ) ^ 2 * (T / s') := by
    ring
  rw [hsplit, ← hBTc]
  linarith

/-- Comptage : les `4k`-cycles `x₀ y₀ ⋯` de triplets dans `D` ont pour masse
`trace (hmat D ^ (2k))` ; on retire ceux où deux `x` coïncident (somme pondérée), puis ceux où un
`y` coïncide avec un autre sommet (au plus `2 (2k)²` paires de positions, chacune de masse
`≤ trace / s'` car les multiplicités non nulles valent au moins `s'`). -/
theorem cycSet_card {W : Type} [Fintype W] (D : Finset (W × W × W)) (k : ℕ) (hk : 2 ≤ k)
    (s' : ℝ) (hs' : 0 < s') (hlow : ∀ t ∈ D, s' ≤ hmat D t.1 t.2.2) :
    trace (hmat D ^ (2 * k)) -
        ∑ x : Fin (2 * k) → W,
          (if ∃ i j : Fin (2 * k), i ≠ j ∧ x i = x j then cycW (hmat D) x else 0) -
        2 * (2 * (k : ℝ)) ^ 2 * trace (hmat D ^ (2 * k)) / s' ≤
      (#(cycSet D (2 * k)) : ℝ) := by
  have h := cycSet_card19 D (2 * k) s' hs' hlow
  rw [total_cycW_eq_trace (hmat D) k hk] at h
  push_cast at h
  exact h

/- ## Lemme 20 : les trois conditions de la définition 2.11 (étape D) -/

/-- Les triplets d'un élément de `cycSet`. -/
private theorem trip20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) (l : ℕ) (hl : l < m) :
    (w ⟨2 * l, by omega⟩, w ⟨2 * l + 1, by omega⟩,
      w ⟨(2 * l + 2) % (2 * m), Nat.mod_lt _ (by omega)⟩) ∈ D := by
  simp only [cycSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact hw.2 ⟨l, hl⟩

private theorem inj20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) : Function.Injective w := by
  simp only [cycSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact hw.1

private theorem val20 {W : Type} {L : ℕ} (w : Fin L → W) (a b : Fin L) (h : a.val = b.val) :
    w a = w b := congrArg w (Fin.ext h)

/-- Condition 1 : sommets distincts, arêtes consécutives. -/
theorem cycSet_adj {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n × Fin n × Fin n))
    (m : ℕ) (hD : ∀ t ∈ D, G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2) :
    ∀ w ∈ cycSet D m, Function.Injective w ∧
      ∀ p : Fin (2 * m), G.Adj (w p) (w ⟨(p.val + 1) % (2 * m), Nat.mod_lt _ p.pos⟩) := by
  intro w hw
  refine ⟨inj20 hw, fun p => ?_⟩
  have hp := p.isLt
  obtain ⟨l, hl | hl⟩ : ∃ l, p.val = 2 * l ∨ p.val = 2 * l + 1 := ⟨p.val / 2, by omega⟩
  · have h := (hD _ (trip20 hw l (by omega))).1
    rwa [val20 w p ⟨2 * l, by omega⟩ hl,
      val20 w ⟨(p.val + 1) % (2 * m), Nat.mod_lt _ p.pos⟩ ⟨2 * l + 1, by omega⟩
        (by simp only; rw [hl, Nat.mod_eq_of_lt (by omega)])]
  · have h := (hD _ (trip20 hw l (by omega))).2
    rwa [val20 w p ⟨2 * l + 1, by omega⟩ hl,
      val20 w ⟨(p.val + 1) % (2 * m), Nat.mod_lt _ p.pos⟩
        ⟨(2 * l + 2) % (2 * m), Nat.mod_lt _ (by omega)⟩ (by simp only; rw [hl])]

/-- Condition 2 : à une position près, un cycle est déterminé par un voisin commun de `v` et
d'un `y` (position paire), ou de deux `x` (position impaire). -/
theorem cycSet_fix {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (D : Finset (Fin n × Fin n × Fin n)) (m : ℕ) (s : ℝ)
    (hD : ∀ t ∈ D, G.Adj v t.1 ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧
      (#(G.neighborFinset v ∩ G.neighborFinset t.2.1) : ℝ) ≤ s ∧
      (#(G.neighborFinset t.1 ∩ G.neighborFinset t.2.2) : ℝ) ≤ s) :
    ∀ y ∈ cycSet D m, ∀ i,
      (#((cycSet D m).filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s := by
  intro y hy i
  have hi := i.isLt
  have hinj : Set.InjOn (fun x : Fin (2 * m) → Fin n => x i)
      ((cycSet D m).filter fun x => ∀ j, j ≠ i → x j = y j) := by
    intro x hx z hz he
    funext j
    by_cases hj : j = i
    · subst hj
      exact he
    · exact ((Finset.mem_filter.mp hx).2 j hj).trans ((Finset.mem_filter.mp hz).2 j hj).symm
  have hne (a : Fin (2 * m)) (h : a.val ≠ i.val) : a ≠ i := fun e => h (congrArg Fin.val e)
  obtain ⟨l, hl | hl⟩ : ∃ l, i.val = 2 * l ∨ i.val = 2 * l + 1 := ⟨i.val / 2, by omega⟩
  · have hA := (hD _ (trip20 hy l (by omega))).2.2.2.1
    refine le_trans ?_ hA
    exact_mod_cast Finset.card_le_card_of_injOn (fun x : Fin (2 * m) → Fin n => x i) (by
      intro x hx
      obtain ⟨hxc, hxy⟩ := Finset.mem_filter.mp hx
      have ht := hD _ (trip20 hxc l (by omega))
      have e1 := val20 x i ⟨2 * l, by omega⟩ hl
      have e2 := hxy ⟨2 * l + 1, by omega⟩ (hne _ (by simp only; omega))
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe,
        SimpleGraph.mem_neighborFinset]
      rw [e1]
      exact ⟨ht.1, e2 ▸ ht.2.1.symm⟩) hinj
  · have hB := (hD _ (trip20 hy l (by omega))).2.2.2.2
    refine le_trans ?_ hB
    exact_mod_cast Finset.card_le_card_of_injOn (fun x : Fin (2 * m) → Fin n => x i) (by
      intro x hx
      obtain ⟨hxc, hxy⟩ := Finset.mem_filter.mp hx
      have ht := hD _ (trip20 hxc l (by omega))
      have e1 := val20 x i ⟨2 * l + 1, by omega⟩ hl
      have e2 := hxy ⟨2 * l, by omega⟩ (hne _ (by simp only; omega))
      have e3 := hxy ⟨(2 * l + 2) % (2 * m), Nat.mod_lt _ (by omega)⟩ (hne _ (by
        simp only
        rcases Nat.lt_or_ge (2 * l + 2) (2 * m) with h | h
        · rw [Nat.mod_eq_of_lt h]; omega
        · rw [show 2 * l + 2 = 2 * m by omega, Nat.mod_self]; omega))
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe,
        SimpleGraph.mem_neighborFinset]
      rw [e1]
      exact ⟨e2 ▸ ht.2.1, e3 ▸ ht.2.2.1.symm⟩) hinj

/-- Fibres : `#A ≤ #(A.image π) * K` si chaque fibre a au plus `K` éléments. -/
private theorem fib20 {β γ : Type} [DecidableEq γ] (A : Finset β) (π : β → γ) (K : ℝ)
    (h : ∀ u0 ∈ A.image π, (#(A.filter fun u => π u = u0) : ℝ) ≤ K) :
    (#A : ℝ) ≤ #(A.image π) * K := by
  rw [Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem π hx)]
  push_cast
  calc ∑ b ∈ A.image π, (#(A.filter fun u => π u = b) : ℝ) ≤ ∑ _b ∈ A.image π, K :=
        Finset.sum_le_sum h
    _ = #(A.image π) * K := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Allonger une fenêtre de lecture de `N` à `M` positions multiplie le nombre de lectures par
au plus `K`, si chaque fibre s'injecte par `φ` dans un ensemble `T u0` de taille `≤ K`. -/
private theorem step20 {α W γ : Type} (C : Finset α) (f : α → ℕ → W) (N M : ℕ) (hNM : N ≤ M)
    (T : (Fin N → W) → Finset γ) (φ : (Fin M → W) → γ) (K : ℝ)
    (hT : ∀ u0, (#(T u0) : ℝ) ≤ K)
    (hmaps : ∀ w ∈ C, φ (fun t => f w t.val) ∈ T (fun t => f w t.val))
    (hinj : ∀ w ∈ C, ∀ w' ∈ C, (∀ t < N, f w t = f w' t) →
      φ (fun t => f w t.val) = φ (fun t => f w' t.val) → ∀ t < M, f w t = f w' t) :
    (#(C.image fun w (t : Fin M) => f w t.val) : ℝ) ≤
      #(C.image fun w (t : Fin N) => f w t.val) * K := by
  have hAB : (C.image fun w (t : Fin M) => f w t.val).image
      (fun u (t : Fin N) => u ⟨t.val, lt_of_lt_of_le t.isLt hNM⟩) =
      C.image fun w (t : Fin N) => f w t.val := by
    rw [Finset.image_image]
    rfl
  rw [← hAB]
  apply fib20 (C.image fun w (t : Fin M) => f w t.val)
    (fun u (t : Fin N) => u ⟨t.val, lt_of_lt_of_le t.isLt hNM⟩) K
  intro u0 _
  refine le_trans (Nat.cast_le.mpr ?_) (hT u0)
  apply Finset.card_le_card_of_injOn φ
  · intro u hu
    obtain ⟨hu, hπ⟩ := Finset.mem_filter.mp hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    rw [← hπ]
    exact hmaps w hw
  · intro u hu u' hu' he
    obtain ⟨hu, hπ⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu', hπ'⟩ := Finset.mem_filter.mp hu'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hu'
    funext t
    exact hinj w hw w' hw' (fun s hs => congrFun (hπ.trans hπ'.symm) ⟨s, hs⟩) he t.val t.isLt

/-- Lectures des `2q+1` premières positions : un départ dans `S`, puis `q` triplets de `D`. -/
private theorem readQ20 {α W : Type} (C : Finset α) (f : α → ℕ → W) (D : Finset (W × W × W))
    (S : Finset W) (Δ R : ℝ) (hS : (#S : ℝ) ≤ Δ) (hR : 0 ≤ R)
    (hrow : ∀ a, (#(rowSet D a) : ℝ) ≤ R) (r : ℕ)
    (h0 : ∀ w ∈ C, f w 0 ∈ S)
    (htr : ∀ w ∈ C, ∀ t < r, (f w (2 * t), f w (2 * t + 1), f w (2 * t + 2)) ∈ D) :
    ∀ q ≤ r, (#(C.image fun w (t : Fin (2 * q + 1)) => f w t.val) : ℝ) ≤ Δ * R ^ q := by
  intro q
  induction q with
  | zero =>
    intro _
    have hc : #(C.image fun w (t : Fin (2 * 0 + 1)) => f w t.val) ≤ #S := by
      apply Finset.card_le_card_of_injOn (fun u => u ⟨0, by omega⟩)
      · intro u hu
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
        exact h0 w hw
      · intro u hu u' hu' he
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hu'
        funext t
        have ht : t = ⟨0, by omega⟩ := Fin.ext (by have := t.isLt; omega)
        subst ht
        exact he
    calc (#(C.image fun w (t : Fin (2 * 0 + 1)) => f w t.val) : ℝ) ≤ #S := by exact_mod_cast hc
      _ ≤ Δ * R ^ 0 := by rw [pow_zero, mul_one]; exact hS
  | succ q ih =>
    intro hq
    calc (#(C.image fun w (t : Fin (2 * (q + 1) + 1)) => f w t.val) : ℝ)
        ≤ #(C.image fun w (t : Fin (2 * q + 1)) => f w t.val) * R :=
          step20 C f (2 * q + 1) (2 * (q + 1) + 1) (by omega)
            (fun u0 => rowSet D (u0 ⟨2 * q, by omega⟩))
            (fun u => (u ⟨2 * q, by omega⟩, u ⟨2 * q + 1, by omega⟩, u ⟨2 * q + 2, by omega⟩))
            R (fun _ => hrow _)
            (fun w hw => by
              show (f w (2 * q), f w (2 * q + 1), f w (2 * q + 2)) ∈ rowSet D (f w (2 * q))
              exact Finset.mem_filter.mpr ⟨htr w hw q (by omega), rfl⟩)
            (fun w _ w' _ hlt he t ht => by
              rcases (show t < 2 * q + 1 ∨ t = 2 * q + 1 ∨ t = 2 * q + 2 by omega) with h | h | h
              · exact hlt t h
              · subst h
                exact congrArg (fun p => p.2.1) he
              · subst h
                exact congrArg (fun p => p.2.2) he)
      _ ≤ Δ * R ^ q * R := mul_le_mul_of_nonneg_right (ih (by omega)) hR
      _ = Δ * R ^ (q + 1) := by rw [pow_succ, mul_assoc]

/-- Lectures des `2r+2` premières positions : `readQ20`, puis un `y` final dans `extSet`. -/
private theorem read20 {α W : Type} (C : Finset α) (f : α → ℕ → W) (D : Finset (W × W × W))
    (S : Finset W) (Δ R E : ℝ) (hS : (#S : ℝ) ≤ Δ) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hrow : ∀ a, (#(rowSet D a) : ℝ) ≤ R) (hext : ∀ a, (#(extSet D a) : ℝ) ≤ E) (r : ℕ)
    (h0 : ∀ w ∈ C, f w 0 ∈ S)
    (htr : ∀ w ∈ C, ∀ t < r, (f w (2 * t), f w (2 * t + 1), f w (2 * t + 2)) ∈ D)
    (hlast : ∀ w ∈ C, f w (2 * r + 1) ∈ extSet D (f w (2 * r))) :
    (#(C.image fun w (t : Fin (2 * r + 2)) => f w t.val) : ℝ) ≤ Δ * R ^ r * E := by
  calc (#(C.image fun w (t : Fin (2 * r + 2)) => f w t.val) : ℝ)
      ≤ #(C.image fun w (t : Fin (2 * r + 1)) => f w t.val) * E :=
        step20 C f (2 * r + 1) (2 * r + 2) (by omega)
          (fun u0 => extSet D (u0 ⟨2 * r, by omega⟩)) (fun u => u ⟨2 * r + 1, by omega⟩)
          E (fun _ => hext _)
          (fun w hw => by
            show f w (2 * r + 1) ∈ extSet D (f w (2 * r))
            exact hlast w hw)
          (fun w _ w' _ hlt he t ht => by
            rcases (show t < 2 * r + 1 ∨ t = 2 * r + 1 by omega) with h | h
            · exact hlt t h
            · subst h
              exact he)
    _ ≤ Δ * R ^ r * E :=
        mul_le_mul_of_nonneg_right (readQ20 C f D S Δ R hS hR hrow r h0 htr r le_rfl) hE

/-- Oubli de deux positions : si les positions gardées se lisent, dans l'ordre `a 0, a 1, …`,
comme un départ dans `S`, `r` triplets de `D` et un `y` final dans `extSet`, alors `Δ R^r E`
fonctions suffisent à décrire `C` hors de `p1` et `p2`. -/
private theorem forget20 {W : Type} {L : ℕ} (C : Finset (Fin L → W)) (D : Finset (W × W × W))
    (S : Finset W) (Δ R E : ℝ) (hS : (#S : ℝ) ≤ Δ) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hrow : ∀ a, (#(rowSet D a) : ℝ) ≤ R) (hext : ∀ a, (#(extSet D a) : ℝ) ≤ E)
    (r : ℕ) (a : ℕ → Fin L) (p1 p2 : Fin L)
    (h0 : ∀ w ∈ C, w (a 0) ∈ S)
    (htr : ∀ w ∈ C, ∀ t < r, (w (a (2 * t)), w (a (2 * t + 1)), w (a (2 * t + 2))) ∈ D)
    (hlast : ∀ w ∈ C, w (a (2 * r + 1)) ∈ extSet D (w (a (2 * r))))
    (hcov : ∀ j, j ≠ p1 → j ≠ p2 → ∃ t < 2 * r + 2, a t = j) :
    ∃ P : Finset (Fin L → W), (#P : ℝ) ≤ Δ * R ^ r * E ∧
      ∀ w ∈ C, ∃ y ∈ P, ∀ j, j ≠ p1 → j ≠ p2 → w j = y j := by
  have hB := read20 C (fun w t => w (a t)) D S Δ R E hS hR hE hrow hext r h0 htr hlast
  refine ⟨(C.image fun w (t : Fin (2 * r + 2)) => w (a t.val)).image
      (fun u j => if h : ∃ t : Fin (2 * r + 2), a t.val = j then u h.choose
        else u ⟨0, by omega⟩), ?_, ?_⟩
  · exact le_trans (by exact_mod_cast Finset.card_image_le) hB
  · intro w hw
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hw), fun j hj1 hj2 => ?_⟩
    obtain ⟨t, ht, hat⟩ := hcov j hj1 hj2
    have hex : ∃ t : Fin (2 * r + 2), a t.val = j := ⟨⟨t, ht⟩, hat⟩
    dsimp only
    rw [dif_pos hex, hex.choose_spec]

/-- `x % n` pour `x < 2n`. -/
private theorem mod20 (x n : ℕ) (h : x < 2 * n) :
    (x < n ∧ x % n = x) ∨ (n ≤ x ∧ x % n = x - n) := by
  rcases Nat.lt_or_ge x n with hx | hx
  · exact Or.inl ⟨hx, Nat.mod_eq_of_lt hx⟩
  · refine Or.inr ⟨hx, ?_⟩
    rw [Nat.mod_eq_sub_mod hx, Nat.mod_eq_of_lt (by omega)]

/-- Le triplet de `cycSet` qui commence en position `2q` (modulo `2m`), pour tout `q`. -/
private theorem tripX20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) (h2m : 0 < 2 * m) (x0 x1 x2 q : ℕ)
    (h0 : x0 = 2 * q) (h1 : x1 = 2 * q + 1) (h2 : x2 = 2 * q + 2) :
    (w ⟨x0 % (2 * m), Nat.mod_lt _ h2m⟩, w ⟨x1 % (2 * m), Nat.mod_lt _ h2m⟩,
      w ⟨x2 % (2 * m), Nat.mod_lt _ h2m⟩) ∈ D := by
  subst h0 h1 h2
  have hm : 0 < m := by omega
  have hqm := Nat.mod_lt q hm
  have h := trip20 hw (q % m) hqm
  have e0 : (2 * q) % (2 * m) = 2 * (q % m) := Nat.mul_mod_mul_left 2 q m
  have e0' : (2 * q) % (2 * m) = (2 * (q % m)) % (2 * m) := by
    rw [e0, Nat.mod_eq_of_lt (show 2 * (q % m) < 2 * m by omega)]
  have e1 : (2 * q + 1) % (2 * m) = 2 * (q % m) + 1 := by
    have e : (2 * q + 1) % (2 * m) = (2 * (q % m) + 1) % (2 * m) :=
      Nat.ModEq.add_right 1 (n := 2 * m) e0'
    rw [e, Nat.mod_eq_of_lt (show 2 * (q % m) + 1 < 2 * m by omega)]
  have e2 : (2 * q + 2) % (2 * m) = (2 * (q % m) + 2) % (2 * m) :=
    Nat.ModEq.add_right 2 (n := 2 * m) e0'
  have k0 : (⟨(2 * q) % (2 * m), Nat.mod_lt _ h2m⟩ : Fin (2 * m)) =
      ⟨2 * (q % m), by omega⟩ := Fin.ext e0
  have k1 : (⟨(2 * q + 1) % (2 * m), Nat.mod_lt _ h2m⟩ : Fin (2 * m)) =
      ⟨2 * (q % m) + 1, by omega⟩ := Fin.ext e1
  have k2 : (⟨(2 * q + 2) % (2 * m), Nat.mod_lt _ h2m⟩ : Fin (2 * m)) =
      ⟨(2 * (q % m) + 2) % (2 * m), Nat.mod_lt _ h2m⟩ := Fin.ext e2
  rw [k0, k1, k2]
  exact h

/-- Le même triplet, retourné par la symétrie de `D`. -/
private theorem tripR20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) (h2m : 0 < 2 * m)
    (hsymm : ∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) (x0 x1 x2 q : ℕ)
    (h0 : x0 = 2 * q + 2) (h1 : x1 = 2 * q + 1) (h2 : x2 = 2 * q) :
    (w ⟨x0 % (2 * m), Nat.mod_lt _ h2m⟩, w ⟨x1 % (2 * m), Nat.mod_lt _ h2m⟩,
      w ⟨x2 % (2 * m), Nat.mod_lt _ h2m⟩) ∈ D :=
  hsymm _ (tripX20 hw h2m x2 x1 x0 q h2 h1 h0)

private theorem first20 {W : Type} [Fintype W] {D : Finset (W × W × W)} {m : ℕ}
    {w : Fin (2 * m) → W} (hw : w ∈ cycSet D m) (h2m : 0 < 2 * m) {S : Finset W}
    (hfirst : ∀ t ∈ D, t.1 ∈ S) (x q : ℕ) (h : x = 2 * q) :
    w ⟨x % (2 * m), Nat.mod_lt _ h2m⟩ ∈ S :=
  hfirst _ (tripX20 hw h2m x (2 * q + 1) (2 * q + 2) q h rfl rfl)

private theorem ext20 {W : Type} {D : Finset (W × W × W)} {a b c : W} (h : (a, b, c) ∈ D) :
    b ∈ extSet D a :=
  Finset.mem_image.mpr ⟨(a, b, c), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

/-- Condition 3 : oublier deux positions consécutives laisse un chemin `x y x ⋯ x y` (lu dans un
sens ou dans l'autre, `D` étant symétrique) : `x` initial dans `S`, `m - 2` triplets complets
(au plus `R` choix chacun), un `y` final dans `extSet` du dernier `x`. -/
theorem cycSet_forget {W : Type} [Fintype W] (D : Finset (W × W × W)) (m : ℕ) (hm : 2 ≤ m)
    (S : Finset W) (Δ R E : ℝ) (hS : (#S : ℝ) ≤ Δ) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hsymm : ∀ t ∈ D, (t.2.2, t.2.1, t.1) ∈ D) (hfirst : ∀ t ∈ D, t.1 ∈ S)
    (hrow : ∀ a, (#(rowSet D a) : ℝ) ≤ R) (hext : ∀ a, (#(extSet D a) : ℝ) ≤ E)
    (i : Fin (2 * m)) :
    let nx : Fin (2 * m) → Fin (2 * m) := fun i => ⟨(i.val + 1) % (2 * m), Nat.mod_lt _ i.pos⟩
    ∃ P : Finset (Fin (2 * m) → W), (#P : ℝ) ≤ Δ * R ^ (m - 2) * E ∧
      ∀ w ∈ cycSet D m, ∃ y ∈ P, ∀ j, j ≠ nx i → j ≠ nx (nx i) → w j = y j := by
  intro nx
  have h2m : 0 < 2 * m := by omega
  have hi := i.isLt
  have hne : ∀ j : Fin (2 * m), j ≠ nx i → j ≠ nx (nx i) →
      j.val ≠ (i.val + 1) % (2 * m) ∧ j.val ≠ ((i.val + 1) % (2 * m) + 1) % (2 * m) :=
    fun j h1 h2 => ⟨fun e => h1 (Fin.ext e), fun e => h2 (Fin.ext e)⟩
  have hm1 := mod20 (i.val + 1) (2 * m) (by omega)
  have hm2 := mod20 ((i.val + 1) % (2 * m) + 1) (2 * m)
    (by have := Nat.mod_lt (i.val + 1) h2m; omega)
  obtain ⟨l, hl | hl⟩ : ∃ l, i.val = 2 * l ∨ i.val = 2 * l + 1 := ⟨i.val / 2, by omega⟩
  · -- `i` pair : lecture à l'envers depuis `i`
    refine forget20 (cycSet D m) D S Δ R E hS hR hE hrow hext (m - 2)
      (fun t => ⟨(i.val + 2 * m - t) % (2 * m), Nat.mod_lt _ h2m⟩) (nx i) (nx (nx i))
      ?_ ?_ ?_ ?_
    · intro w hw
      exact first20 hw h2m hfirst (i.val + 2 * m - 0) (l + m) (by omega)
    · intro w hw t ht
      exact tripR20 hw h2m hsymm (i.val + 2 * m - 2 * t) (i.val + 2 * m - (2 * t + 1))
        (i.val + 2 * m - (2 * t + 2)) (l + m - t - 1) (by omega) (by omega) (by omega)
    · intro w hw
      exact ext20 (tripR20 hw h2m hsymm (i.val + 2 * m - 2 * (m - 2))
        (i.val + 2 * m - (2 * (m - 2) + 1)) (2 * l + 2) (l + 1) (by omega) (by omega)
        (by omega))
    · intro j hj1 hj2
      obtain ⟨hj1', hj2'⟩ := hne j hj1 hj2
      have hj := j.isLt
      by_cases hji : j.val ≤ i.val
      · refine ⟨i.val - j.val, by omega, Fin.ext ?_⟩
        show (i.val + 2 * m - (i.val - j.val)) % (2 * m) = j.val
        have := mod20 (i.val + 2 * m - (i.val - j.val)) (2 * m) (by omega)
        omega
      · refine ⟨i.val + 2 * m - j.val, by omega, Fin.ext ?_⟩
        show (i.val + 2 * m - (i.val + 2 * m - j.val)) % (2 * m) = j.val
        have := mod20 (i.val + 2 * m - (i.val + 2 * m - j.val)) (2 * m) (by omega)
        omega
  · -- `i` impair : lecture directe depuis `i + 3`
    refine forget20 (cycSet D m) D S Δ R E hS hR hE hrow hext (m - 2)
      (fun t => ⟨(i.val + 3 + t) % (2 * m), Nat.mod_lt _ h2m⟩) (nx i) (nx (nx i))
      ?_ ?_ ?_ ?_
    · intro w hw
      exact first20 hw h2m hfirst (i.val + 3 + 0) (l + 2) (by omega)
    · intro w hw t ht
      exact tripX20 hw h2m (i.val + 3 + 2 * t) (i.val + 3 + (2 * t + 1))
        (i.val + 3 + (2 * t + 2)) (l + 2 + t) (by omega) (by omega) (by omega)
    · intro w hw
      exact ext20 (tripX20 hw h2m (i.val + 3 + 2 * (m - 2)) (i.val + 3 + (2 * (m - 2) + 1))
        (2 * (l + m) + 2) (l + m) (by omega) (by omega) rfl)
    · intro j hj1 hj2
      obtain ⟨hj1', hj2'⟩ := hne j hj1 hj2
      have hj := j.isLt
      by_cases hji : i.val + 3 ≤ j.val
      · refine ⟨j.val - (i.val + 3), by omega, Fin.ext ?_⟩
        show (i.val + 3 + (j.val - (i.val + 3))) % (2 * m) = j.val
        have := mod20 (i.val + 3 + (j.val - (i.val + 3))) (2 * m) (by omega)
        omega
      · refine ⟨j.val + 2 * m - (i.val + 3), by omega, Fin.ext ?_⟩
        show (i.val + 3 + (j.val + 2 * m - (i.val + 3))) % (2 * m) = j.val
        have := mod20 (i.val + 3 + (j.val + 2 * m - (i.val + 3))) (2 * m) (by omega)
        omega

/- ## Lemme 21 : asymptotique (étape E) -/

private theorem growth21 (C a b : ℝ) (h : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ)^a ≤ (n : ℝ)^b := by
  have ht := ((tendsto_rpow_atTop (sub_pos.mpr h)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht] with n hn hc
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ (n : ℝ)^(b-a) * (n : ℝ)^a := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add hn', sub_add_cancel]

private theorem sqrt21 {q d N T S P : ℝ} (hT : 0 < T) (hP : 0 ≤ P)
    (hS : S ≤ N^d * T^(1-d)) (hcoef : 64*q^2*P*N^d ≤ T^d) :
    2*q * Real.sqrt (P*S*T) ≤ T/4 := by
  by_cases h : P*S*T ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos h, mul_zero]; positivity
  have hbound : 64*q^2*P*S ≤ T := calc
    _ ≤ 64*q^2*P*(N^d*T^(1-d)) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (64*q^2*P*N^d)*T^(1-d) := by ring
    _ ≤ T^d*T^(1-d) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = T := by rw [← Real.rpow_add hT, show d+(1-d) = 1 by ring, Real.rpow_one]
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt (le_of_not_ge h)]
  nlinarith only [mul_le_mul_of_nonneg_right hbound hT.le]

/-- Une puissance du facteur polylogarithmique `log n · (⌊log₂ n⌋ + 1)²` est négligeable devant
`n ^ b`. -/
private theorem logpow21 (b C : ℝ) (m : ℕ) (hb : 0 < b) (hC : 0 ≤ C) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      C * (Real.log n * ((Nat.log 2 n : ℝ) + 1) ^ 2) ^ m ≤ (n : ℝ) ^ b := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := b / (12 * m) with hδ
  have hδ0 : 0 < δ := by positivity
  filter_upwards [eventually_ge_atTop 3, growth21 (1/δ) δ (2*δ) (by linarith),
    growth21 (3/δ) δ (2*δ) (by linarith), growth21 C (b/2) b (by linarith)]
    with n hn h1 h2 h3
  have hN3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < n := by linarith
  have hlog : Real.log n ≤ (n:ℝ)^δ / δ := Real.log_le_rpow_div hN0.le hδ0
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    linarith
  have hnl : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
    have hpow : ((2:ℕ):ℝ)^(Nat.log 2 n) ≤ (n:ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have h4 := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at h4
    have h5 := Real.log_two_gt_d9
    push_cast at h4
    nlinarith
  have hL : Real.log n ≤ (n:ℝ)^(2*δ) := by
    calc _ ≤ (n:ℝ)^δ/δ := hlog
      _ = 1/δ * (n:ℝ)^δ := by ring
      _ ≤ _ := h1
  have hJ : (Nat.log 2 n : ℝ) + 1 ≤ (n:ℝ)^(2*δ) := by
    calc _ ≤ 3 * Real.log n := by linarith
      _ ≤ 3 * ((n:ℝ)^δ/δ) := by linarith
      _ = 3/δ * (n:ℝ)^δ := by ring
      _ ≤ _ := h2
  have hJ0 : (0:ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  have hG0 : 0 ≤ Real.log n * ((Nat.log 2 n : ℝ) + 1) ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hG : Real.log n * ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤ (n:ℝ)^(b/2/m) := by
    calc _ ≤ (n:ℝ)^(2*δ) * ((n:ℝ)^(2*δ))^2 := by gcongr
      _ = (n:ℝ)^(b/2/m) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
        congr 1
        rw [hδ]; push_cast; field_simp; ring
  have hGm : (Real.log n * ((Nat.log 2 n : ℝ) + 1) ^ 2)^m ≤ (n:ℝ)^(b/2) := by
    calc _ ≤ ((n:ℝ)^(b/2/m))^m := pow_le_pow_left₀ hG0 hG m
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        field_simp
  calc _ ≤ C * (n:ℝ)^(b/2) := mul_le_mul_of_nonneg_left hGm hC
    _ ≤ _ := h3

set_option maxHeartbeats 1000000 in
/-- Les inégalités numériques de la preuve, pour `n` grand. `Q = #c4`, `Dc = #D`, `T` et `T'`
les traces `2·(2k)` et `2·(2k-1)` de `hmat D`, `Δ = K n^(1/3+ε)`,
`U = 96 log n / n^(4/3+ε) · Q`. -/
theorem h2_asymp (ε K : ℝ) (hε : 0 < ε) (hε6 : ε < 1 / 6) (hK : 0 < K) (k : ℕ)
    (hk : 1 / ε ≤ k) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      ∀ Q Dc s s' T T' : ℝ,
        8 * (n : ℝ) ^ (5 / 3 + 3 * ε) / (96 * Real.log n) ≤ Q →
        Q ≤ 2 * n * ((Nat.log 2 n : ℝ) + 1) ^ 2 * Dc →
        0 < s → s ≤ 2 * (K * (n : ℝ) ^ (1 / 3 + ε)) →
        Dc ≤ 2 * s' * (K * (n : ℝ) ^ (1 / 3 + ε)) ^ 2 →
        (Dc / (K * (n : ℝ) ^ (1 / 3 + ε))) ^ (2 * (2 * k)) ≤ T →
        T' ≤ (n : ℝ) ^ (1 / ((2 * k : ℕ) : ℝ)) * T ^ (1 - 1 / ((2 * k : ℕ) : ℝ)) →
        0 < T ∧
        2 * ((2 * k : ℕ) : ℝ) * Real.sqrt (((2 * k : ℕ) : ℝ) * s *
            (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * Q) * T' * T) ≤ T / 4 ∧
        2 * (2 * ((2 * k : ℕ) : ℝ)) ^ 2 * T / s' ≤ T / 4 ∧
        K * (n : ℝ) ^ (1 / 3 + ε) *
            (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * Q) ^ (2 * (2 * k) - 2) *
            (4 * (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * Q) / s) ≤
          (n : ℝ) ^ (-(ε / 2)) * (T / 2) / (16 * k * s) := by
  have hk6 : (6:ℝ) < k := lt_of_lt_of_le ((lt_div_iff₀ hε).mpr (by linarith)) hk
  have hk1 : 1 ≤ k * ε := (div_le_iff₀ hε).mp hk
  have hk0 : (0:ℝ) < k := by linarith
  have hk7 : 6 < k := by exact_mod_cast hk6
  set q : ℝ := ((2 * k : ℕ) : ℝ) with hq
  have hqv : q = 2 * (k:ℝ) := by rw [hq]; push_cast; ring
  have hq0 : 0 < q := by rw [hqv]; linarith
  have hdq : 1 / q ≤ ε / 2 := by
    rw [div_le_iff₀ hq0, hqv]; nlinarith
  have hLd : ((2 * (2 * k) : ℕ) : ℝ) * (1 / q) = 2 := by
    rw [hqv]; push_cast; field_simp
  obtain ⟨p, hp⟩ : ∃ p, 2 * (2 * k) - 2 = p := ⟨_, rfl⟩
  have hp2 : 2 * (2 * k) = p + 2 := by omega
  filter_upwards [eventually_ge_atTop 3,
    logpow21 (ε/2) (589824*q^3*K^3) 2 (by positivity) (by positivity) (by norm_num),
    logpow21 (ε/2) (1536*q^2*K^2) 1 (by positivity) (by positivity) (by norm_num),
    logpow21 (ε/2) (3072*k*K^2*(192*K)^(p+1)) (p+2) (by positivity) (by positivity) (by omega)]
    with n hn g2 g3 g4
  refine ⟨by omega, ?_⟩
  intro Q Dc s s' T T' hQ hQD hs0 hs hDs' hT hT'
  have hN3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < n := by linarith
  have hL0 : 0 < Real.log n := Real.log_pos (by linarith)
  have e43 : (n:ℝ) ^ (4/3+ε) = n * (n:ℝ) ^ (1/3+ε) := by
    rw [show (4/3:ℝ)+ε = 1 + (1/3+ε) by ring, Real.rpow_add hN0 1, Real.rpow_one]
  have e53 : (n:ℝ) ^ (5/3+3*ε) = n * ((n:ℝ) ^ (1/3+ε))^2 * ((n:ℝ) ^ (ε/2))^2 := by
    rw [show (5/3:ℝ)+3*ε = 1 + (1/3+ε) + (1/3+ε) + (ε/2+ε/2) by ring,
      Real.rpow_add hN0 (1 + (1/3+ε) + (1/3+ε)), Real.rpow_add hN0 (1 + (1/3+ε)),
      Real.rpow_add hN0 1, Real.rpow_add hN0 (ε/2), Real.rpow_one]
    ring
  have eneg : (n:ℝ) ^ (-(ε/2)) = ((n:ℝ) ^ (ε/2))⁻¹ := Real.rpow_neg hN0.le _
  have e1q : (n:ℝ) ^ (1/q) ≤ (n:ℝ) ^ (ε/2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hdq
  rw [e53] at hQ
  rw [e43, eneg, hp]
  set N : ℝ := (n:ℝ) with hNdef
  set L := Real.log N with hLdef
  set J : ℝ := (Nat.log 2 n : ℝ) + 1 with hJdef
  have hJ1 : 1 ≤ J := by
    rw [hJdef]; have := (Nat.log 2 n).cast_nonneg (α := ℝ); linarith
  set G := L * J^2 with hGdef
  have hG0 : 0 < G := by positivity
  set A := N ^ (1/3+ε) with hAdef
  have hA0 : 0 < A := by positivity
  set h := N ^ (ε/2) with hhdef
  have hh1 : 1 ≤ h := Real.one_le_rpow (by linarith) (by positivity)
  have hh0 : 0 < h := by linarith
  set U := 96 * L / (N * A) * Q with hUdef
  -- Q > 0, Dc > 0
  have hQ' : 8*(N*A^2*h^2) ≤ 96*L*Q := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 96*L)).mp hQ
    linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hU0 : 0 ≤ U := by rw [hUdef]; positivity
  have hDc0 : 0 < Dc := by
    by_contra hc
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0:ℝ) ≤ 2*N*J^2) (not_lt.mp hc)
    linarith
  obtain ⟨x, hx0, rfl⟩ : ∃ x, 0 < x ∧ Dc = K*A*x :=
    ⟨Dc/(K*A), by positivity, by field_simp⟩
  rw [mul_div_cancel_left₀ x (by positivity : K*A ≠ 0)] at hT
  have hTpos : 0 < T := lt_of_lt_of_le (pow_pos hx0 _) hT
  -- (i)
  have hi : A*h^2 ≤ 24*K*G*x := by
    have h1 : 8*(N*A^2*h^2) ≤ 96*L*(2*N*J^2*(K*A*x)) :=
      hQ'.trans (mul_le_mul_of_nonneg_left hQD (by positivity))
    have h2 : (A*h^2) * (8*N*A) ≤ (24*K*G*x) * (8*N*A) := by
      calc (A*h^2)*(8*N*A) = 8*(N*A^2*h^2) := by ring
      _ ≤ 96*L*(2*N*J^2*(K*A*x)) := h1
      _ = (24*K*G*x)*(8*N*A) := by rw [hGdef]; ring
    exact le_of_mul_le_mul_right h2 (by positivity)
  -- (ii)
  have hii : U ≤ 192*K*G*x := by
    rw [hUdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc 96*L*Q ≤ 96*L*(2*N*J^2*(K*A*x)) := mul_le_mul_of_nonneg_left hQD (by positivity)
    _ = _ := by rw [hGdef]; ring
  -- (iii)
  have hroot : x^2 ≤ T^(1/q) := calc
    x^2 = (x^(2*(2*k)))^(1/q) := by
      rw [← Real.rpow_natCast x (2*(2*k)), ← Real.rpow_mul hx0.le, hLd, Real.rpow_two]
    _ ≤ T^(1/q) := Real.rpow_le_rpow (by positivity) hT (by positivity)
  -- 2e conclusion
  have hkey2 : 24576*q^3*K^2*A*G*h ≤ x := by
    have h1 : (24576*q^3*K^2*A*G*h) * (24*K*G) ≤ x * (24*K*G) := by
      calc (24576*q^3*K^2*A*G*h) * (24*K*G) = (589824*q^3*K^3*G^2) * (A*h) := by ring
      _ ≤ h * (A*h) := mul_le_mul_of_nonneg_right g2 (by positivity)
      _ = A*h^2 := by ring
      _ ≤ 24*K*G*x := hi
      _ = x*(24*K*G) := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hcoef : 64*q^2*(q*s*U)*N^(1/q) ≤ T^(1/q) := calc
    64*q^2*(q*s*U)*N^(1/q) ≤ 64*q^2*(q*(2*(K*A))*(192*K*G*x))*h := by gcongr
    _ = (24576*q^3*K^2*A*G*h)*x := by ring
    _ ≤ x * x := mul_le_mul_of_nonneg_right hkey2 hx0.le
    _ = x^2 := by ring
    _ ≤ T^(1/q) := hroot
  -- 3e conclusion
  have hx2 : x ≤ 2*s'*K*A := by
    have h1 : (K*A)*x ≤ (K*A)*(2*s'*K*A) := by
      calc (K*A)*x ≤ 2*s'*(K*A)^2 := hDs'
      _ = _ := by ring
    exact le_of_mul_le_mul_left h1 (by positivity)
  have hs'0 : 0 < s' := by
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (by positivity : (0:ℝ) ≤ K*A)
    linarith [lt_of_lt_of_le hx0 hx2]
  have h32 : 32*q^2 ≤ s' := by
    have h1 : (32*q^2) * (48*K^2*G*A) ≤ s' * (48*K^2*G*A) := by
      calc (32*q^2) * (48*K^2*G*A) = (1536*q^2*K^2*G^1) * A := by ring
      _ ≤ h * A := mul_le_mul_of_nonneg_right g3 hA0.le
      _ ≤ h^2 * A := by gcongr; nlinarith
      _ = A*h^2 := by ring
      _ ≤ 24*K*G*x := hi
      _ ≤ 24*K*G*(2*s'*K*A) := by gcongr
      _ = s' * (48*K^2*G*A) := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hthird : 2 * (2 * q) ^ 2 * T / s' ≤ T / 4 := by
    rw [div_le_iff₀ hs'0]
    nlinarith [mul_le_mul_of_nonneg_left h32 hTpos.le]
  -- 4e conclusion
  have hkey4 : 128*k*K*A*h*(192*K*G)^(p+1) ≤ x := by
    have h1 : (128*k*K*A*h*(192*K*G)^(p+1)) * (24*K*G) ≤ x * (24*K*G) := by
      calc (128*k*K*A*h*(192*K*G)^(p+1)) * (24*K*G)
          = (3072*k*K^2*(192*K)^(p+1)*G^(p+2)) * (A*h) := by ring_nf
      _ ≤ h * (A*h) := mul_le_mul_of_nonneg_right g4 (by positivity)
      _ = A*h^2 := by ring
      _ ≤ 24*K*G*x := hi
      _ = x*(24*K*G) := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hmain : 128*k*K*A*h*U^(p+1) ≤ T := calc
    128*k*K*A*h*U^(p+1) ≤ 128*k*K*A*h*(192*K*G*x)^(p+1) := by gcongr
    _ = (128*k*K*A*h*(192*K*G)^(p+1)) * x^(p+1) := by ring_nf
    _ ≤ x * x^(p+1) := mul_le_mul_of_nonneg_right hkey4 (by positivity)
    _ = x^(p+2) := by ring
    _ ≤ T := by rw [← hp2]; exact hT
  have hlhs : K*A*U^p*(4*U/s) = 128*k*K*A*h*U^(p+1) / (32*k*s*h) := by
    field_simp
    ring
  have hrhs : h⁻¹*(T/2)/(16*k*s) = T/(32*k*s*h) := by
    field_simp
    ring
  refine ⟨hTpos, sqrt21 hTpos (by positivity) hT' hcoef, hthird, ?_⟩
  rw [hlhs, hrhs]
  exact div_le_div_of_nonneg_right hmain (by positivity)

end E147H2

open E147H2 in
set_option maxHeartbeats 2000000 in
theorem OMA.solution : OMA.R_Erdos147_erdos_147_variants_cubic_R1.H2 := by
  classical
  intro ε K hε hε6 hK k hk
  have hkpos : 0 < k := by
    by_contra! hz
    have hzero : k = 0 := by omega
    rw [hzero, Nat.cast_zero] at hk
    exact (not_lt_of_ge hk) (by positivity)
  have hk2 : 2 ≤ 2 * k := by omega
  filter_upwards [h2_asymp ε K hε hε6 hK k hk] with n hn
  obtain ⟨hn2, hnum⟩ := hn
  intro G c4 nxt₀ hdeg hQ hU
  let next (L : ℕ) (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
  let result (L : ℕ) : Prop := ∃ C : Finset (Fin L → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
    (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (next L i))) ∧
    (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
    ∀ i : Fin L, ∃ P : Finset (Fin L → Fin n),
      (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
      ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ next L i → j ≠ next L (next L i) → x j = y j
  change result (8 * k)
  rw [show 8 * k = 2 * (2 * (2 * k)) by ring]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hQpos : 0 < (#c4 : ℝ) := lt_of_lt_of_le
    (div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hnpos _)) (mul_pos (by norm_num) hlog)) hQ
  have hU0 : 0 ≤ 96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * (#c4 : ℝ) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hlog.le) (Real.rpow_nonneg hnpos.le _))
      hQpos.le
  have hQnat : 0 < #c4 := Nat.cast_pos.mp hQpos
  obtain ⟨v, s, s', D, hs, hs2, hs', hQD, hD, hsymm, hlow, hDc, hhs, hrowU, hext⟩ :=
    stepAB G (K * (n : ℝ) ^ (1 / 3 + ε)) (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4)
      hdeg hU hQnat
  have hQD' : (#c4 : ℝ) ≤ 2 * n * ((Nat.log 2 n : ℝ) + 1) ^ 2 * #D := hQD
  have hDpos : 0 < #D := by
    rcases Nat.eq_zero_or_pos (#D) with h0 | h0
    · rw [h0, Nat.cast_zero, mul_zero] at hQD'
      linarith
    · exact h0
  obtain ⟨t₀, ht₀⟩ := Finset.card_pos.mp hDpos
  have hpos : ∃ u w, 0 < hmat D u w := ⟨t₀.1, t₀.2.2, lt_of_lt_of_le hs' (hlow t₀ ht₀)⟩
  have hfirst : ∀ t ∈ D, t.1 ∈ G.neighborFinset v :=
    fun t ht => (G.mem_neighborFinset v t.1).2 (hD t ht).1
  have hSne : (G.neighborFinset v).Nonempty := ⟨t₀.1, hfirst t₀ ht₀⟩
  have hScard : (#(G.neighborFinset v) : ℝ) ≤ K * (n : ℝ) ^ (1 / 3 + ε) := by
    rw [G.card_neighborFinset_eq_degree]
    exact hdeg v
  have hSpos : 0 < (#(G.neighborFinset v) : ℝ) := by exact_mod_cast hSne.card_pos
  have hsid := sidorenko_supp (hmat D) (hmat_symm D hsymm) (G.neighborFinset v) hSne
    (hmat_supp D _ hfirst hsymm) (2 * k)
  rw [hmat_sum] at hsid
  have hT : ((#D : ℝ) / (K * (n : ℝ) ^ (1 / 3 + ε))) ^ (2 * (2 * k)) ≤
      trace (hmat D ^ (2 * (2 * k))) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) ?_ _) hsid
    exact div_le_div_of_nonneg_left (by positivity) hSpos hScard
  have hint := trace_interp_M (hmat D) (hmat_nonneg D) (hmat_symm D hsymm) hpos (2 * k)
    (by omega)
  rw [Fintype.card_fin] at hint
  obtain ⟨hTpos, hTT, hYY, hlast⟩ := hnum (#c4) (#D) s s' _ _ hQ hQD' hs hs2 hDc
    (by convert hT using 0; congr!) hint
  have hrot := bad_le_rot (hmat D) (hmat_nonneg D) Eq (fun _ _ h => h.symm) (2 * k) hk2
  have hrow : ∀ a, ∑ b, hmat D a b ≤ 96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4 :=
    fun a => (hmat_row D a).trans_le (hrowU a)
  have hanch := conflictM_le (hmat D) (hmat_nonneg D) (hmat_symm D hsymm) Eq
    (fun _ _ h => h.symm) s _ hs.le hU0 (fun b e => by
      refine le_of_eq_of_le ?_ (hhs b e)
      refine (Finset.sum_eq_single e ?_ ?_).trans ?_
      · intro a _ hae
        exact if_neg (Ne.symm hae)
      · intro h
        exact absurd (mem_univ e) h
      · exact if_pos rfl) hrow (2 * k) hk2
  have hbad := (hrot.trans (mul_le_mul_of_nonneg_left hanch (by positivity))).trans hTT
  have hcard := cycSet_card D (2 * k) hk2 s' hs' hlow
  have hCpos : 0 < (#(cycSet D (2 * (2 * k))) : ℝ) := by linarith
  have hD' : ∀ t ∈ D, G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 :=
    fun t ht => ⟨(hD t ht).2.1, (hD t ht).2.2.1⟩
  have hadj := cycSet_adj G D (2 * (2 * k)) hD'
  refine ⟨cycSet D (2 * (2 * k)), Finset.card_pos.mp (by exact_mod_cast hCpos), s, hs,
    fun x hx => hadj x hx, cycSet_fix G v D _ s hD, fun i => ?_⟩
  have hext' : ∀ a, (#(extSet D a) : ℝ) ≤
      4 * (96 * Real.log n / (n : ℝ) ^ (4 / 3 + ε) * #c4) / s :=
    fun a => (le_div_iff₀ hs).2 (hext a)
  obtain ⟨P, hP, hP'⟩ := cycSet_forget D (2 * (2 * k)) (by omega) (G.neighborFinset v)
    (K * (n : ℝ) ^ (1 / 3 + ε)) _ _ hScard hU0 (by positivity) hsymm hfirst hrowU hext' i
  refine ⟨P, hP.trans (hlast.trans ?_), hP'⟩
  gcongr
  linarith
