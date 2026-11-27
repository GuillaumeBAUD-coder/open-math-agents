import OMAReductions.R_Erdos147_erdos_147_variants_cubic_R1
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Étape `H1` de la réduction R1 d'Erdős 147 (variante cubique)

Lemme 2.14 de Janzer (arXiv 2109.06110) : peu de 4-cycles donnent un ensemble bon de
`8k`-cycles. Preuve : cycles homomorphes comptés par la matrice d'adjacence `A`
(`T_m = trace (A^(2m))`), Sidorenko pour les cycles pairs, bornes de Cauchy–Schwarz des cycles en
conflit (sommets répétés, codegrés), puis les conditions de la définition 2.11. Plan :
`plan-h1.md`.
-/

-- Credit: @iLc0

open SimpleGraph Finset Filter Asymptotics Matrix
open scoped Classical

namespace E147H1

/-- Poids d'un uplet cyclique `x : Fin L → W` : produit des `M (x i) (x (i+1 mod L))`. -/
noncomputable def cycW {W : Type} [Fintype W] (M : Matrix W W ℝ) {L : ℕ} (x : Fin L → W) : ℝ :=
  ∏ i : Fin L, M (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩)

/-- Matrice d'adjacence réelle de `G`. -/
noncomputable def adjR {W : Type} [Fintype W] (G : SimpleGraph W) : Matrix W W ℝ :=
  fun u v => if G.Adj u v then 1 else 0

/- ## Déjà prouvés pour `H3` (lemmes 9, 10, 11) -/

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

/- ## Lemme 12 : cycles homomorphes en conflit, version adjacence -/

private theorem trip12 {W : Type} [Fintype W] (M : Matrix W W ℝ) (k : ℕ) (hk : 2 ≤ k)
    (F : W → W → W → ℝ) :
    ∑ x : Fin (2*k) → W, cycW M x * F (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) =
    ∑ a, ∑ b, ∑ c, M a b * (M^k) b c * (M^(k-1)) c a * F a b c := by
  classical
  rw [cyc_split M k 1 hk (by omega) (by omega) (fun a b _ c => F a b c)]
  simp [Matrix.one_apply, mul_ite, ite_mul, sum_ite_irrel]

private theorem nn12 {W : Type} [Fintype W] (G : SimpleGraph W) (a b : W) :
    0 ≤ adjR G a b := by unfold adjR; split <;> positivity

private theorem symm12 {W : Type} [Fintype W] (G : SimpleGraph W) (n : ℕ) (u v : W) :
    (adjR G ^ n) u v = (adjR G ^ n) v u := by
  have h : (adjR G).IsSymm := by
    ext a b
    change (if G.Adj b a then (1:ℝ) else 0) = _
    simp only [adjR, G.adj_comm b a]
  exact (h.pow n).apply v u

private theorem row12 {W : Type} [Fintype W] (G : SimpleGraph W) (a : W) :
    ∑ b, adjR G a b = (G.degree a : ℝ) := by
  simp only [adjR, sum_boole, ← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]

private theorem trace12 {W : Type} [Fintype W] (M : Matrix W W ℝ) (p q : ℕ) :
    trace (M ^ (p+q)) = ∑ a, ∑ b, (M^p) a b * (M^q) b a := by
  simp only [pow_add, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem ratio12 {U V : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V) : V * (U / V) ≤ U := by
  by_cases h : V = 0
  · simp [h, hU]
  · exact le_of_eq (by field_simp)

private theorem upperFirst12 {W : Type} [Fintype W] (G : SimpleGraph W)
    (Δ : ℝ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2*k) → W, cycW (adjR G) x *
      (((adjR G)^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) /
       ((adjR G)^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩)) ≤
    Δ * trace (adjR G ^ (2*(k-1))) := by
  classical
  let M := adjR G
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg (nn12 G)
  rw [trip12 (adjR G) k hk (fun a b c => (P (k-1)) a c / (P k) b c),
    two_mul, trace12, mul_sum]
  apply sum_le_sum
  intro a _
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro c _
  calc
    _ ≤ ∑ b, M a b * ((P (k-1)) a c * (P (k-1)) c a) := by
      apply sum_le_sum
      intro b _
      have hh := mul_le_mul_of_nonneg_left (ratio12 (hn (k-1) a c) (hn k b c))
        (mul_nonneg (nn12 G a b) (hn (k-1) c a))
      dsimp [M, P] at *
      linarith only [hh]
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right ((row12 G a).le.trans (hdeg a))
        (mul_nonneg (hn _ _ _) (hn _ _ _))

private theorem mass12 {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (n : ℕ) (b e c : W) :
    ∑ a, (if r a e then adjR G a b * (adjR G^n) c a / (adjR G^n) a c else 0) ≤
      (#((G.neighborFinset b).filter (r e)) : ℝ) := by
  classical
  calc
    _ ≤ ∑ a, if G.Adj b a ∧ r e a then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro a _
      rw [symm12 G n c a]
      by_cases h : r a e
      · by_cases hab : G.Adj a b
        · rw [if_pos h, if_pos ⟨hab.symm, hr a e h⟩]
          simp only [adjR, if_pos hab, one_mul]
          exact div_self_le_one _
        · have hba : ¬ G.Adj b a := fun h' => hab h'.symm
          simp [h,adjR,hab,hba]
      · simp only [if_neg h]
        split <;> norm_num
    _ = _ := by
      rw [sum_boole]
      have he : univ.filter (fun a => G.Adj b a ∧ r e a) = (G.neighborFinset b).filter (r e) := by
        ext a
        simp
      rw [he]

private theorem upperOne12 {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (s : ℝ)
    (k j : ℕ) (hk : 2 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k)
    (hrel : ∀ b e, (adjR G ^ (j-1)) b e ≠ 0 →
      (#((G.neighborFinset b).filter (r e)) : ℝ) ≤ s) :
    ∑ x : Fin (2*k) → W, cycW (adjR G) x *
      (if r (x ⟨0,by omega⟩) (x ⟨j,by omega⟩) then
       ((adjR G)^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       ((adjR G)^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) else 0) ≤
    s * trace (adjR G ^ (2*k)) := by
  classical
  let M := adjR G
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg (nn12 G)
  rw [cyc_split (adjR G) k j hk hj hjk
    (fun a b e c => if r a e then (P k) b c / (P (k-1)) a c else 0),
    two_mul, trace12, mul_sum]
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
      by_cases hz : (P (j-1)) b e = 0
      · simp [f, hz]
      have hh := (mass12 G r hr (k-1) b e c).trans (hrel b e hz)
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hh
        (mul_nonneg (mul_nonneg (hn _ _ _) (hn _ _ _)) (hn _ _ _)))
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      dsimp [f, P, M]
      by_cases hr' : r a e <;> simp [hr']
      ring
    _ = s * ((P k) b c * (P k) b c) := by
      rw [← mul_sum, ← sum_mul]
      have hp : (∑ e, (P (j-1)) b e * (P (k+1-j)) e c) = (P k) b c := by
        change ((M^(j-1)) * (M^(k+1-j))) b c = _
        rw [← pow_add, show j-1 + (k+1-j) = k by omega]
      rw [hp]
    _ = _ := by
      exact congrArg (fun z => s * ((P k) b c * z)) (symm12 G k b c)

private theorem cwNonneg12 {W : Type} [Fintype W] (G : SimpleGraph W) {N : ℕ}
    (x : Fin N → W) : 0 ≤ cycW (adjR G) x :=
  prod_nonneg (fun _ _ => nn12 G _ _)

private theorem support12 {W : Type} [Fintype W] (G : SimpleGraph W)
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (2*k) → W) (hx : cycW (adjR G) x ≠ 0) :
    (adjR G^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 ∧
    (adjR G^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 := by
  classical
  let M := adjR G
  let P := fun n : ℕ => M^n
  let bad := fun a b c : W => if (P (k-1)) a c = 0 ∨ (P k) b c = 0 then (1:ℝ) else 0
  let term := fun y : Fin (2*k) → W => cycW M y * bad (y ⟨0,by omega⟩) (y ⟨1,by omega⟩)
    (y ⟨k+1,by omega⟩)
  have hzero : ∑ y, term y = 0 := by
    dsimp only [term]
    rw [trip12 M k hk bad]
    apply sum_eq_zero
    intro a _
    apply sum_eq_zero
    intro b _
    apply sum_eq_zero
    intro c _
    by_cases ha : (P (k-1)) a c = 0
    · have hc : (P (k-1)) c a = 0 := (symm12 G (k-1) c a).trans ha
      change _ * (P (k-1)) c a * _ = 0
      simp [hc]
    · by_cases hb : (P k) b c = 0
      · change _ * (P k) b c * _ * _ = 0
        simp [hb]
      · simp [bad, ha, hb]
  have hn (y) (_ : y ∈ univ) : 0 ≤ term y := by
    dsimp only [term,bad]
    exact mul_nonneg (cwNonneg12 G y) (by split <;> norm_num)
  have hh := (sum_eq_zero_iff_of_nonneg hn).mp hzero x (mem_univ x)
  dsimp only [term,bad] at hh
  by_contra! h
  have h' : (P (k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) = 0 ∨
      (P k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) = 0 := by tauto
  rw [if_pos h', mul_one] at hh
  exact hx hh

private theorem cs12 {W : Type} [Fintype W] (G : SimpleGraph W)
    (Δ : ℝ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (k : ℕ) (hk : 2 ≤ k)
    (hit : (Fin (2*k) → W) → Prop) (C : ℝ)
    (hsecond : ∑ x : Fin (2*k) → W, (if hit x then cycW (adjR G) x else 0) *
      ((adjR G^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       (adjR G^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩)) ≤ C) :
    (∑ x, if hit x then cycW (adjR G) x else 0) ≤
      Real.sqrt ((Δ * trace (adjR G ^ (2*(k-1)))) * C) := by
  classical
  let X := Fin (2*k) → W
  let M := adjR G
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let T := fun x : X => if hit x then cycW M x else 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg (nn12 G)
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  have hT (x : X) : 0 ≤ T x := by
    dsimp only [T]
    split
    · exact cwNonneg12 G x
    · rfl
  have hf (x : X) : 0 ≤ T x * (A x / B x) := mul_nonneg (hT x) (div_nonneg (hA x) (hB x))
  have hg (x : X) : 0 ≤ T x * (B x / A x) := mul_nonneg (hT x) (div_nonneg (hB x) (hA x))
  have cs := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset X)
    (fun x _ => hf x) (fun x _ => hg x) (r := T) (by
      intro x _
      by_cases h : cycW M x = 0
      · simp [T,h]
      · obtain ⟨h₁,h₂⟩ := support12 G k hk x h
        have h₁' : A x ≠ 0 := h₁
        have h₂' : B x ≠ 0 := h₂
        apply le_of_eq
        field_simp [h₁',h₂'])
  have hfirst : ∑ x, T x * (A x / B x) ≤ Δ * trace (P (2*(k-1))) := by
    apply le_trans _ (upperFirst12 G Δ hdeg k hk)
    apply sum_le_sum
    intro x _
    change T x * (A x / B x) ≤ cycW M x * (A x / B x)
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (hA x) (hB x))
    dsimp only [T]
    split
    · rfl
    · exact cwNonneg12 G x
  apply Real.le_sqrt_of_sq_le
  change (∑ x, T x)^2 ≤ _
  exact cs.trans (mul_le_mul hfirst hsecond (sum_nonneg (fun x _ => hg x))
    (le_trans (sum_nonneg (fun x _ => hf x)) hfirst))

/-- Cycles homomorphes en conflit depuis la position 0 (lemme 2.1 de [Ja20], forme trace). -/
theorem conflictA_le {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (s Δ : ℝ) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ)
    (hrel : ∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤ s)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ j : Fin (2 * k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (x ⟨0, by omega⟩) (x j)
          then cycW (adjR G) x else 0) ≤
      Real.sqrt (k * s * Δ * trace (adjR G ^ (2 * (k - 1))) * trace (adjR G ^ (2 * k))) := by
  classical
  have _hsΔ := mul_nonneg hs hΔ
  let X := Fin (2*k) → W
  let M := adjR G
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let hit := fun x : X =>
    ∃ j : Fin (2*k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (a x) (x j)
  let T := fun x : X => @ite ℝ (hit x) (Classical.propDecidable _) (cycW M x) 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg (nn12 G)
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  let idx := fun p : Fin k => (⟨p.val+1,by omega⟩ : Fin (2*k))
  let term := fun (x : X) (p : Fin k) =>
    cycW M x * (if r (a x) (x (idx p)) then B x / A x else 0)
  have hterm (x p) : 0 ≤ term x p := by
    apply mul_nonneg (cwNonneg12 G x)
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
        exact upperOne12 G r hr s k (p.val+1) hk (by omega) (by omega) (fun b e _ => hrel e b)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ = ∑ x : X, T x := by
      apply sum_congr rfl
      intro x _
      by_cases h : hit x <;> simp only [T, hit, a] at h ⊢ <;> simp [h, M]
    _ ≤ _ := cs12 G Δ hdeg k hk hit ((k:ℝ) * (s * trace (adjR G ^ (2*k)))) hsecond
    _ = _ := congrArg Real.sqrt (by ring)

/-- Cycles homomorphes dont les positions 0 et 2 sont en relation ; la relation n'est bornée
qu'entre les deux bouts d'une arête. -/
theorem conflict2_le {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (s Δ : ℝ) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ)
    (hrel : ∀ b e, G.Adj b e → (#((G.neighborFinset b).filter (r e)) : ℝ) ≤ s)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if r (x ⟨0, by omega⟩) (x ⟨2, by omega⟩) then cycW (adjR G) x else 0) ≤
      Real.sqrt (s * Δ * trace (adjR G ^ (2 * (k - 1))) * trace (adjR G ^ (2 * k))) := by
  classical
  have _hsΔ := mul_nonneg hs hΔ
  let hit := fun x : Fin (2*k) → W => r (x ⟨0,by omega⟩) (x ⟨2,by omega⟩)
  have hlocal (b e : W) (h : (adjR G ^ (2-1)) b e ≠ 0) :
      (#((G.neighborFinset b).filter (r e)) : ℝ) ≤ s := by
    apply hrel b e
    by_contra hn
    exact h (by simp [adjR,hn])
  have hsecond := upperOne12 G r hr s k 2 hk (by omega) hk hlocal
  refine (cs12 G Δ hdeg k hk hit (s * trace (adjR G ^ (2*k))) ?_).trans_eq
    (congrArg Real.sqrt (by ring))
  simpa only [hit, ite_mul, mul_ite, zero_mul, mul_zero] using hsecond

/- ## Lemme 13 : traces de la matrice d'adjacence, Sidorenko, rotations -/

theorem adjR_nonneg {W : Type} [Fintype W] (G : SimpleGraph W) (u v : W) :
    0 ≤ adjR G u v := by
  unfold adjR
  split <;> positivity

theorem cycW_adjR {W : Type} [Fintype W] (G : SimpleGraph W) {L : ℕ} (x : Fin L → W) :
    cycW (adjR G) x =
      if ∀ i : Fin L, G.Adj (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩) then 1 else 0 := by
  classical
  split_ifs with h
  · exact Finset.prod_eq_one (fun i _ => if_pos (h i))
  · obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)

private theorem powNonneg13 {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ) (a b : W) :
    0 ≤ (adjR G ^ m) a b := Matrix.pow_apply_nonneg (adjR_nonneg G) m a b

private theorem symm13 {W : Type} [Fintype W] (G : SimpleGraph W) : (adjR G).IsSymm := by
  ext a b
  change (if G.Adj b a then (1:ℝ) else 0) = _
  simp only [adjR, G.adj_comm b a]

theorem one_le_trace_adjR {W : Type} [Fintype W] (G : SimpleGraph W)
    (hG : G.edgeFinset.Nonempty) (k : ℕ) : 1 ≤ trace (adjR G ^ (2 * k)) := by
  classical
  obtain ⟨u,v,huv⟩ := ne_bot_iff_exists_adj.mp (edgeFinset_nonempty.mp hG)
  have h₂ : 1 ≤ (adjR G ^ 2) u u := by
    rw [sq, Matrix.mul_apply]
    calc
      1 = adjR G u v * adjR G v u := by simp [adjR,huv,huv.symm]
      _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (adjR_nonneg G u z) (adjR_nonneg G z u))
        (mem_univ v)
  have hdiag : 1 ≤ (adjR G ^ (2 * k)) u u := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, Matrix.mul_apply]
      calc
        1 ≤ (adjR G ^ (2 * k)) u u * (adjR G ^ 2) u u := one_le_mul_of_one_le_of_one_le ih h₂
        _ ≤ _ := single_le_sum (fun z _ => mul_nonneg (powNonneg13 G _ u z) (powNonneg13 G 2 z u))
          (mem_univ u)
  exact hdiag.trans (single_le_sum (fun z _ => powNonneg13 G (2*k) z z) (mem_univ u))

private theorem traceSplit13 {W : Type} [Fintype W] (G : SimpleGraph W) (a b : ℕ) :
    trace (adjR G ^ (a + b)) = ∑ p : W × W, (adjR G ^ a) p.1 p.2 * (adjR G ^ b) p.2 p.1 := by
  simp [pow_add, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Log-convexité des traces paires. -/
private theorem logConvex13 {W : Type} [Fintype W] (G : SimpleGraph W) (j : ℕ) (hj : 1 ≤ j) :
    trace (adjR G ^ (2 * j)) ^ 2 ≤
      trace (adjR G ^ (2 * (j - 1))) * trace (adjR G ^ (2 * (j + 1))) := by
  let a := j - 1
  let b := j + 1
  rw [show 2 * j = a + b by dsimp [a, b]; omega, traceSplit13,
      show 2 * (j - 1) = a + a by dsimp [a]; omega, traceSplit13,
      show 2 * (j + 1) = b + b by dsimp [b]; omega, traceSplit13]
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun _ _ ↦ mul_nonneg (powNonneg13 ..) (powNonneg13 ..)
  · exact fun _ _ ↦ mul_nonneg (powNonneg13 ..) (powNonneg13 ..)
  · rintro ⟨u, v⟩ _
    dsimp only
    rw [((symm13 G).pow a).apply u v, ((symm13 G).pow b).apply u v]
    exact le_of_eq (by ring)

/-- Log-convexité des traces paires, avec `T_0 = |W|`. -/
theorem trace_adjR_interp {W : Type} [Fintype W] (G : SimpleGraph W)
    (hG : G.edgeFinset.Nonempty) (k : ℕ) (hk : 1 ≤ k) :
    trace (adjR G ^ (2 * (k - 1))) ≤
      (Fintype.card W : ℝ) ^ (1 / (k : ℝ)) * trace (adjR G ^ (2 * k)) ^ (1 - 1 / (k : ℝ)) := by
  let T (n : ℕ) := trace (adjR G ^ (2 * n))
  have pos (n : ℕ) : 0 < T n := lt_of_lt_of_le zero_lt_one (one_le_trace_adjR G hG n)
  let a (n : ℕ) := Real.log (T n)
  have step (n : ℕ) : a (n + 1) - a n ≤ a (n + 2) - a (n + 1) := by
    have h : T (n + 1) ^ 2 ≤ T n * T (n + 2) := by
      simpa [T] using logConvex13 G (n + 1) (by omega)
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
  apply (Real.log_le_log_iff (pos _) (mul_pos (Real.rpow_pos_of_pos (pos _) _) (Real.rpow_pos_of_pos (pos _) _))).mp
  rw [Real.log_mul (Real.rpow_pos_of_pos (pos _) _).ne' (Real.rpow_pos_of_pos (pos _) _).ne',
    Real.log_rpow (pos _), Real.log_rpow (pos _)]
  change a n ≤ 1 / ((n + 1 : ℕ) : ℝ) * a 0 + (1 - 1 / ((n + 1 : ℕ) : ℝ)) * a (n + 1)
  push_cast
  field_simp
  linarith [bound n]

-- Recopié de la preuve fusionnée de Sidorenko pour les cycles pairs (PR #641, adaptée de la PR #478).
private theorem symmetricTrace13 {N k : ℕ} (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    ((1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A a b) ^ (2 * k) ≤
      (A ^ (2 * k)).trace := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
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
  let v : Fin N → ℝ := fun _ => 1 / Real.sqrt (N : ℝ)
  have hvv : v ⬝ᵥ v = 1 := by
    simp only [dotProduct, v]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hNpos)
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    field_simp [hsq_ne, ne_of_gt hNpos]
    linarith
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
  have hquad_lhs : v ⬝ᵥ (A.mulVec v) = (1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A a b := by
    simp only [dotProduct, Matrix.mulVec, v, Finset.mul_sum]
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp [hsq_ne, ne_of_gt hNpos]
    rw [Real.sq_sqrt (le_of_lt hNpos)]
    ring
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
  rw [← hquad_lhs, hquad_rhs, htr]
  exact le_trans hjensen hle_tr

/-- Sidorenko pour les cycles pairs, forme trace (lemme 2.6 de l'article). -/
theorem sidorenko_adjR {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) (k : ℕ) :
    (2 * (#G.edgeFinset : ℝ) / n) ^ (2 * k) ≤ trace (adjR G ^ (2 * k)) := by
  have hA : (adjR G).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact symm13 G
  have hs := symmetricTrace13 (k := k) hn (adjR G) hA
  have hrow (u : Fin n) : ∑ v, adjR G u v = (G.degree u : ℝ) := by
    simp only [adjR, sum_boole, ← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
  simp_rw [hrow] at hs
  have hsum : (∑ a, (G.degree a : ℝ)) = 2 * (#G.edgeFinset : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hs
  simpa only [div_eq_inv_mul, mul_one] using hs

/-- Union sur les rotations pour un conflit entre les positions `i` et `i + 2`. -/
theorem bad2_le_rot {W : Type} [Fintype W] (M : Matrix W W ℝ) (hM : ∀ u v, 0 ≤ M u v)
    (r : W → W → Prop) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ i : Fin (2 * k), r (x i) (x ⟨(i.val + 2) % (2 * k), Nat.mod_lt _ i.pos⟩)
          then cycW M x else 0) ≤
      2 * k * ∑ x : Fin (2 * k) → W,
        (if r (x ⟨0, by omega⟩) (x ⟨2, by omega⟩) then cycW M x else 0) := by
  classical
  let : NeZero (2 * k) := ⟨by omega⟩
  let I := Fin (2 * k)
  let rot (s : I) (x : I → W) := fun i : I ↦ x (i + s)
  let q : I := ⟨2,by omega⟩
  let good (x : I → W) := r (x 0) (x q)
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
  change _ ≤ 2 * (k : ℝ) * ∑ x : I → W, B x
  calc
    _ ≤ ∑ x : I → W, ∑ s : I, B (rot s x) := by
      apply sum_le_sum
      intro x _
      split
      · rename_i hx
        obtain ⟨s,hr⟩ := hx
        have hs : good (rot s x) := by
          change r (x (0+s)) (x (q+s))
          rw [zero_add, add_comm q s]
          exact hr
        calc
          cycW M x = B (rot s x) := by simp [B, hs, cyc]
          _ ≤ _ := single_le_sum (fun z _ ↦ bpos (rot z x)) (mem_univ s)
      · exact sum_nonneg fun _ _ ↦ bpos _
    _ = _ := by rw [sum_comm]; simp [reindex, I]

/- ## Lemme 15 : codegrés, conditions 2 et 3 de la définition 2.11 -/

open scoped Fin.NatCast in
private theorem shift15 {L : ℕ} [NeZero L] (i : Fin L) (a : ℕ) :
    (⟨(i.val + a) % L, Nat.mod_lt _ i.pos⟩ : Fin L) = i + (a : Fin L) := by
  apply Fin.ext
  simp [Fin.val_add]

private theorem paths15 {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (m : ℕ) :
    (#(univ.filter fun z : Fin (m + 1) → Fin n => ∀ j : Fin m,
        G.Adj (z j.castSucc) (z j.succ)) : ℝ) ≤ n * Δ ^ m := by
  classical
  let P (l : ℕ) := univ.filter fun z : Fin (l + 1) → Fin n =>
    ∀ j : Fin l, G.Adj (z j.castSucc) (z j.succ)
  change (#(P m) : ℝ) ≤ _
  induction m with
  | zero => simp [P]
  | succ m ih =>
    let U := (P m).sigma fun z => G.neighborFinset (z 0)
    have hcard : #(P (m+1)) ≤ #U := by
      apply card_le_card_of_injOn (fun z : Fin (m + 2) → Fin n =>
        (⟨Fin.tail z, z 0⟩ : Σ _ : Fin (m + 1) → Fin n, Fin n))
      · intro z hz
        have hz' := (mem_filter.mp hz).2
        apply mem_sigma.mpr
        refine ⟨mem_filter.mpr ⟨mem_univ _, fun j => hz' j.succ⟩, ?_⟩
        exact (G.mem_neighborFinset _ _).mpr (hz' 0).symm
      · intro z _ w _ h
        have ht := congrArg Sigma.fst h
        have hh := congrArg (fun q : Σ _ : Fin (m + 1) → Fin n, Fin n => q.2) h
        change Fin.tail z = Fin.tail w at ht
        change z 0 = w 0 at hh
        rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail w, ht, hh]
    calc
      (#(P (m+1)) : ℝ) ≤ #U := by exact_mod_cast hcard
      _ = ∑ z ∈ P m, (G.degree (z 0) : ℝ) := by simp [U]
      _ ≤ ∑ _z ∈ P m, Δ := Finset.sum_le_sum (fun z _ => hdeg (z 0))
      _ = (#(P m) : ℝ) * Δ := by simp
      _ ≤ n * Δ ^ m * Δ := mul_le_mul_of_nonneg_right ih hΔ
      _ = n * Δ ^ (m + 1) := by rw [pow_succ, mul_assoc]

/-- Chaque `a ∈ N(b)`, `a ≠ e`, de codegré `> t` avec `e` donne au moins `t - 1` 4-cycles
étiquetés `(e, b, a, y)` qui passent par l'arête `s(e, b)`. -/
theorem codeg_bound {n : ℕ} (G : SimpleGraph (Fin n)) (t B : ℝ) (b e : Fin n) (hbe : G.Adj b e)
    (hB : (#(((univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter fun q =>
          G.Adj q.1 q.2.1 ∧ G.Adj q.2.1 q.2.2.1 ∧ G.Adj q.2.2.1 q.2.2.2 ∧ G.Adj q.2.2.2 q.1 ∧
            q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2).filter fun q =>
          s(e, b) = s(q.1, q.2.1) ∨ s(e, b) = s(q.2.1, q.2.2.1) ∨
            s(e, b) = s(q.2.2.1, q.2.2.2) ∨ s(e, b) = s(q.2.2.2, q.1)) : ℝ) ≤ B) :
    (#((G.neighborFinset b).filter fun a =>
        e ≠ a ∧ t < (#(G.neighborFinset e ∩ G.neighborFinset a) : ℝ)) : ℝ) * (t - 1) ≤ B := by
  classical
  let S := (G.neighborFinset b).filter fun a =>
    e ≠ a ∧ t < (#(G.neighborFinset e ∩ G.neighborFinset a) : ℝ)
  let U (a : Fin n) := (G.neighborFinset e ∩ G.neighborFinset a).erase b
  have hu (a) (ha : a ∈ S) : t - 1 ≤ (#(U a) : ℝ) := by
    obtain ⟨hba, _, hgt⟩ := mem_filter.mp ha
    have hb : b ∈ G.neighborFinset e ∩ G.neighborFinset a :=
      mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hbe.symm,
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hba).symm⟩
    dsimp only [U]
    rw [Finset.cast_card_erase_of_mem hb]
    linarith
  apply le_trans _ hB
  calc
    _ = ∑ _a ∈ S, (t - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ S, (#(U a) : ℝ) := Finset.sum_le_sum hu
    _ = (#(S.sigma U) : ℝ) := by simp
    _ ≤ _ := by
      exact_mod_cast (Finset.card_le_card_of_injOn
        (fun q : Σ _ : Fin n, Fin n => (e, b, q.1, q.2)) (s := S.sigma U) (by
          rintro ⟨a, y⟩ h
          obtain ⟨ha, hy⟩ := mem_sigma.mp h
          obtain ⟨hba, hea, _⟩ := mem_filter.mp ha
          obtain ⟨hyb, hya⟩ := mem_erase.mp hy
          obtain ⟨hey, hay⟩ := mem_inter.mp hya
          apply mem_filter.mpr
          exact ⟨mem_filter.mpr ⟨mem_univ _, hbe.symm, (G.mem_neighborFinset _ _).mp hba,
            (G.mem_neighborFinset _ _).mp hay, ((G.mem_neighborFinset _ _).mp hey).symm, hea, hyb.symm⟩, Or.inl rfl⟩) (by
          rintro ⟨a, y⟩ _ ⟨a', y'⟩ _ h
          change (e, b, a, y) = (e, b, a', y') at h
          obtain ⟨rfl, rfl⟩ : a = a' ∧ y = y' := by simpa using h
          rfl))

open scoped Fin.NatCast Fin.CommRing in
/-- Condition 2 : à une position près, un cycle homomorphe est déterminé par un voisin commun
de ses deux voisins. -/
theorem fix1_card {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℕ) (hL : 3 ≤ L) (s : ℝ)
    (C : Finset (Fin L → Fin n))
    (hC : ∀ x ∈ C, (∀ i : Fin L, G.Adj (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩)) ∧
      ∀ i : Fin L, (#(G.neighborFinset (x i) ∩
        G.neighborFinset (x ⟨(i.val + 2) % L, Nat.mod_lt _ i.pos⟩)) : ℝ) ≤ s) :
    ∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s := by
  classical
  let : NeZero L := ⟨by omega⟩
  intro y hy i
  let p := i - 1
  have hp1 : p + 1 = i := sub_add_cancel _ _
  have hp2 : p + 2 = i + 1 := by dsimp [p]; ring
  have hone : (1 : Fin L) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < L)] at hv
  have hn : i + 1 ≠ i := fun h => hone (add_left_cancel (show i + 1 = i + 0 by rwa [add_zero]))
  have hp : p ≠ i := fun h => hn ((congrArg (· + 1) h.symm).trans hp1)
  have hbound := (hC y hy).2 p
  rw [shift15, Nat.cast_ofNat, hp2] at hbound
  apply le_trans _ hbound
  exact_mod_cast (card_le_card_of_injOn (fun x : Fin L → Fin n => x i) (by
    intro x hx
    obtain ⟨hxc, hxy⟩ := mem_filter.mp hx
    have h1 := (hC x hxc).1 p
    have h2 := (hC x hxc).1 i
    rw [shift15, Nat.cast_one, hp1, hxy p hp] at h1
    rw [shift15, Nat.cast_one, hxy _ hn] at h2
    exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr h1, (G.mem_neighborFinset _ _).mpr h2.symm⟩) (by
    intro x hx z hz he
    funext j
    by_cases hj : j = i
    · exact hj ▸ he
    · exact ((mem_filter.mp hx).2 j hj).trans ((mem_filter.mp hz).2 j hj).symm))

open scoped Fin.NatCast Fin.CommRing in
/-- Condition 3 : oublier deux positions consécutives d'un cycle homomorphe laisse un chemin à
`L - 3` arêtes, d'où au plus `|W| Δ^(L-3)` images. -/
theorem forget2_card {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (L : ℕ) (hL : 3 ≤ L) (C : Finset (Fin L → Fin n))
    (hC : ∀ x ∈ C, ∀ i : Fin L, G.Adj (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩))
    (i : Fin L) :
    let nx : Fin L → Fin L := fun i => ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
    ∃ P : Finset (Fin L → Fin n), (#P : ℝ) ≤ n * Δ ^ (L - 3) ∧
      ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ nx i → j ≠ nx (nx i) → x j = y j := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
  intro nx
  have hnx (j) : nx j = j + 1 := by simpa only [Nat.cast_one] using shift15 j 1
  let P := univ.filter fun z : Fin (m + 1) → Fin n => ∀ j : Fin m, G.Adj (z j.castSucc) (z j.succ)
  let expand (z : Fin (m + 1) → Fin n) (j : Fin (m + 3)) : Fin n :=
    if h : (i - j).val < m + 1 then z ⟨(i - j).val, h⟩ else z 0
  refine ⟨P.image expand, ?_, ?_⟩
  · calc
      (#(P.image expand) : ℝ) ≤ #P := by exact_mod_cast (card_image_le : #(P.image expand) ≤ #P)
      _ ≤ n * Δ ^ m := paths15 G Δ hΔ hdeg m
      _ = _ := by simp
  · intro x hx
    let z (t : Fin (m + 1)) := x (i - (t.val : Fin (m + 3)))
    have hz : z ∈ P := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, fun j => ?_⟩
      have ha := (hC x hx (i - ((j.val : Fin (m + 3)) + 1))).symm
      rw [shift15, Nat.cast_one] at ha
      have hshift : i - ((j.val : Fin (m + 3)) + 1) + 1 = i - (j.val : Fin (m + 3)) := by abel
      simpa only [z, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, hshift] using ha
    refine ⟨expand z, mem_image_of_mem _ hz, fun j hj₁ hj₂ => ?_⟩
    have hwrap : (m : Fin (m + 3)) + 3 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using Fin.natCast_self (m + 3)
    have hback : (((i - j).val : ℕ) : Fin (m + 3)) = i - j := by simp
    have hsmall : (i - j).val < m + 1 := by
      by_contra! hn
      have hlt := (i - j).isLt
      have he : (i - j).val = m + 1 ∨ (i - j).val = m + 2 := by omega
      rcases he with he | he
      · apply hj₂
        rw [hnx, hnx]
        rw [he, Nat.cast_add, Nat.cast_one] at hback
        linear_combination hback - hwrap
      · apply hj₁
        rw [hnx]
        rw [he, Nat.cast_add, Nat.cast_ofNat] at hback
        linear_combination hback - hwrap
    simp only [expand, dif_pos hsmall, z, hback]
    simp

/- ## Lemme 16 : asymptotique -/

private theorem growth16 (C a b : ℝ) (h : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ)^a ≤ (n : ℝ)^b := by
  have ht := ((tendsto_rpow_atTop (sub_pos.mpr h)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht] with n hn hc
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ (n : ℝ)^(b-a) * (n : ℝ)^a := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add hn', sub_add_cancel]

private theorem sqrt16 {q d N T S P : ℝ} (hT : 0 < T) (hP : 0 ≤ P)
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

private theorem last16 {ε K N a T : ℝ} {k L : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hmin : (N^a / 3)^L ≤ T)
    (hbig : (32*(k:ℝ)*3^L*K^(L-3)) * N^(1+a*(↑(L-3) : ℝ)+2*ε+ε/2) ≤ N^(a*(L:ℝ))) :
    N * (K*N^a)^(L-3) ≤ N^(-(ε/2)) * (T/2) / (16*k*N^(2*ε)) := by
  have hthree : (0:ℝ) < 3^L := by positivity
  rw [div_pow] at hmin
  rw [Real.rpow_mul hN.le a (L : ℝ), Real.rpow_natCast] at hbig
  have h := hbig.trans ((div_le_iff₀ hthree).mp hmin)
  have hprod : N*(K*N^a)^(L-3)*(16*k*N^(2*ε))*(2*N^(ε/2)) ≤ T := by
    apply (le_of_mul_le_mul_right _ hthree)
    calc
      _ = (32*(k:ℝ)*3^L*K^(L-3)) * N^(1+a*(↑(L-3) : ℝ)+2*ε+ε/2) := by
        rw [mul_pow, Real.rpow_add hN, Real.rpow_add hN, Real.rpow_add hN, Real.rpow_one,
          Real.rpow_mul hN.le a (↑(L-3) : ℝ), Real.rpow_natCast]
        ring
      _ ≤ _ := h
  apply (le_div_iff₀ (by positivity)).mpr
  rw [Real.rpow_neg hN.le, ← div_eq_inv_mul]
  apply (le_div_iff₀ (by positivity)).mpr
  linarith only [hprod]

/-- Les inégalités numériques de la preuve, pour `n` grand (`K4 = 4k`, `L = 8k`). -/
theorem h1_asymp (ε K : ℝ) (hε : 0 < ε) (hε6 : ε < 1 / 6) (hK : 0 < K) (k : ℕ)
    (hk : 1 / ε ≤ k) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 2 ≤ (n : ℝ) ^ (2 * ε) ∧
      ∀ E T T' : ℝ, (n : ℝ) ^ (4 / 3 + ε) / 6 ≤ E → (2 * E / n) ^ (2 * (4 * k)) ≤ T →
        T' ≤ (n : ℝ) ^ (1 / ((4 * k : ℕ) : ℝ)) * T ^ (1 - 1 / ((4 * k : ℕ) : ℝ)) →
        0 < T ∧
        2 * ((4 * k : ℕ) : ℝ) *
            Real.sqrt (((4 * k : ℕ) : ℝ) * 1 * (K * (n : ℝ) ^ (1 / 3 + ε)) * T' * T) ≤ T / 4 ∧
        2 * ((4 * k : ℕ) : ℝ) *
            Real.sqrt (8 * (n : ℝ) ^ (1 / 3 + 2 * ε) / ((n : ℝ) ^ (2 * ε) - 1) *
              (K * (n : ℝ) ^ (1 / 3 + ε)) * T' * T) ≤ T / 4 ∧
        (n : ℝ) * (K * (n : ℝ) ^ (1 / 3 + ε)) ^ (2 * (4 * k) - 3) ≤
          (n : ℝ) ^ (-(ε / 2)) * (T / 2) / (16 * k * (n : ℝ) ^ (2 * ε)) := by
  let q : ℝ := ((4*k : ℕ) : ℝ)
  let L := 2*(4*k)
  let d : ℝ := 1/q
  let a : ℝ := 1/3+ε
  have hkpos : 0 < k := by
    have hh : (6:ℝ) < k := lt_of_lt_of_le ((lt_div_iff₀ hε).mpr (by linarith only [hε6])) hk
    exact_mod_cast (lt_trans (by norm_num : (0:ℝ) < 6) hh)
  have hq : 0 < q := by dsimp [q]; positivity
  have hd : 0 < d := one_div_pos.mpr hq
  have hdε : d ≤ ε/4 := by
    apply (div_le_iff₀ hq).mpr
    have hh := (div_le_iff₀ hε).mp hk
    dsimp [q]; push_cast; linarith
  have hp : (L : ℝ)*d = 2 := by
    dsimp [L,d,q]; push_cast; field_simp
  have he₁ : a+d < 2*a := by dsimp [a]; linarith
  have he₂ : 1/3+a+d < 2*a := by dsimp [a]; linarith
  have he₃ : 1+a*(↑(L-3) : ℝ)+2*ε+ε/2 < a*(L:ℝ) := by
    rw [Nat.cast_sub (by dsimp [L]; omega : 3 ≤ L)]
    dsimp [a]; linarith
  have ht := ((tendsto_rpow_atTop (show 0 < 2*ε by positivity)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht, growth16 (576*q^3*K) _ _ he₁,
    growth16 (9216*q^2*K) _ _ he₂, growth16 (32*(k:ℝ)*3^L*K^(L-3)) _ _ he₃]
    with n hn h2 h₁ h₂ h₃
  let N : ℝ := n
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (by omega : 0 < n)
  refine ⟨hn,h2,?_⟩
  intro E T T' hE hT hT'
  have hbase : N^a/3 ≤ 2*E/N := by
    apply (le_div_iff₀ hN).mpr
    change N^(4/3+ε)/6 ≤ E at hE
    rw [show 4/3+ε = a+1 by dsimp [a]; ring, Real.rpow_add hN, Real.rpow_one] at hE
    linarith
  have hmin : (N^a/3)^L ≤ T := (pow_le_pow_left₀ (by positivity) hbase L).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hmin
  have hroot : N^(2*a)/9 ≤ T^d := calc
    _ = (N^a/3)^2 := by rw [mul_comm (2:ℝ), Real.rpow_mul hN.le, Real.rpow_two]; ring
    _ = ((N^a/3)^L)^d := by
      rw [← Real.rpow_natCast _ L, ← Real.rpow_mul (by positivity), hp, Real.rpow_two]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hmin hd.le
  have hfirst : 64*q^2*(q*1*(K*N^a))*N^d ≤ T^d := by
    apply le_trans _ hroot
    change 576*q^3*K*N^(a+d) ≤ N^(2*a) at h₁
    rw [Real.rpow_add hN] at h₁
    linarith only [h₁]
  have hs : 8*N^(1/3+2*ε)/(N^(2*ε)-1) ≤ 16*N^(1/3:ℝ) := by
    change 2 ≤ N^(2*ε) at h2
    apply (div_le_iff₀ (by linarith)).mpr
    rw [Real.rpow_add hN]
    nlinarith only [mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN.le (1/3))]
  have hsecond : 64*q^2*((8*N^(1/3+2*ε)/(N^(2*ε)-1))*(K*N^a))*N^d ≤ T^d := by
    apply le_trans _ hroot
    calc
      _ ≤ 64*q^2*((16*N^(1/3:ℝ))*(K*N^a))*N^d := by gcongr
      _ ≤ _ := by
        change 9216*q^2*K*N^(1/3+a+d) ≤ N^(2*a) at h₂
        rw [Real.rpow_add hN, Real.rpow_add hN] at h₂
        linarith only [h₂]
  have hden : 0 ≤ N^(2*ε)-1 := by change 2 ≤ N^(2*ε) at h2; linarith
  exact ⟨hTpos, sqrt16 hTpos (by positivity) hT' hfirst,
    sqrt16 hTpos (by positivity) hT' hsecond, last16 hN hkpos hmin h₃⟩

end E147H1

private theorem diff14 {L : ℕ} (hL : 3 ≤ L) (i : Fin L) :
    i ≠ ⟨(i.val + 2) % L, Nat.mod_lt _ i.pos⟩ := by
  intro he
  have h := congrArg Fin.val he
  change i.val = (i.val + 2) % L at h
  by_cases hb : i.val + 2 < L
  · rw [Nat.mod_eq_of_lt hb] at h
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : L ≤ i.val + 2), Nat.mod_eq_of_lt (by omega)] at h
    omega

open E147H1 in
set_option maxHeartbeats 2000000 in
theorem OMA.solution : OMA.R_Erdos147_erdos_147_variants_cubic_R1.H1 := by
  classical
  intro ε K hε hε6 hK k hk
  have hkpos : 0 < k := by
    by_contra! hz
    have hzero : k = 0 := by omega
    rw [hzero, Nat.cast_zero] at hk
    exact (not_lt_of_ge hk) (by positivity)
  let m := 4 * k
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hL : 3 ≤ 2 * m := by omega
  filter_upwards [h1_asymp ε K hε hε6 hK k hk] with n hn
  obtain ⟨hn1, hn2, hnum⟩ := hn
  intro G c4 nxt₀ hE hdeg hc4
  let next (L : ℕ) (i : Fin L) : Fin L := ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩
  let result (L : ℕ) : Prop := ∃ C : Finset (Fin L → Fin n), C.Nonempty ∧ ∃ s : ℝ, 0 < s ∧
    (∀ x ∈ C, Function.Injective x ∧ ∀ i, G.Adj (x i) (x (next L i))) ∧
    (∀ y ∈ C, ∀ i, (#(C.filter fun x => ∀ j, j ≠ i → x j = y j) : ℝ) ≤ s) ∧
    ∀ i : Fin L, ∃ P : Finset (Fin L → Fin n),
      (#P : ℝ) ≤ (n : ℝ) ^ (-(ε / 2)) * #C / (16 * k * s) ∧
      ∀ x ∈ C, ∃ y ∈ P, ∀ j, j ≠ next L i → j ≠ next L (next L i) → x j = y j
  change result (8 * k)
  rw [show 8 * k = 2 * m by dsimp [m]; ring]
  let nxt := next (2 * m)
  let A := adjR G
  let T := trace (A ^ (2 * m))
  let T' := trace (A ^ (2 * (m - 1)))
  let Δ := K * (n : ℝ) ^ (1 / 3 + ε)
  let s := (n : ℝ) ^ (2 * ε)
  let B := 8 * (n : ℝ) ^ (1 / 3 + 2 * ε)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsm : 0 < s - 1 := by change 2 ≤ s at hn2; linarith
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hG : G.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (show 0 < (#G.edgeFinset : ℝ) from lt_of_lt_of_le (by positivity) hE)
  have hT := sidorenko_adjR hn1 G m
  have hT' := trace_adjR_interp G hG m (by omega)
  rw [Fintype.card_fin] at hT'
  obtain ⟨hpos, hrep, hcodeg, hlast⟩ := hnum (#G.edgeFinset) T T' hE hT (by
    dsimp only [T, T', A, m]
    dsimp only [m] at hT'
    convert hT' using 0
    congr!)
  let r : Fin n → Fin n → Prop := fun u w =>
    u ≠ w ∧ s < (#(G.neighborFinset u ∩ G.neighborFinset w) : ℝ)
  have hr : ∀ u w, r u w → r w u := by
    intro u w h
    exact ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩
  have hrel : ∀ b e, G.Adj b e → (#((G.neighborFinset b).filter (r e)) : ℝ) ≤ B / (s - 1) := by
    intro b e he
    apply (le_div_iff₀ hsm).2
    exact codeg_bound G s B b e he (hc4 s(e, b) (by simpa using he.symm))
  let bad₁ (x : Fin (2 * m) → Fin n) := ∃ i j, i ≠ j ∧ x i = x j
  let two (i : Fin (2 * m)) : Fin (2 * m) := ⟨(i.val + 2) % (2 * m), Nat.mod_lt _ i.pos⟩
  let bad₂ (x : Fin (2 * m) → Fin n) := ∃ i, r (x i) (x (two i))
  have hrel₁ (u v : Fin n) : (#((G.neighborFinset v).filter (Eq u)) : ℝ) ≤ 1 := by
    have hsub : (G.neighborFinset v).filter (Eq u) ⊆ {u} := by
      intro w hw
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hw).2.symm
    exact_mod_cast (show #((G.neighborFinset v).filter (Eq u)) ≤ 1 by
      simpa only [Finset.card_singleton] using Finset.card_le_card hsub)
  have hS₁ : (∑ x, if bad₁ x then cycW A x else 0) ≤ T / 4 := by
    have hrot := bad_le_rot A (adjR_nonneg G) Eq (fun _ _ h => h.symm) m hm
    have hanch := conflictA_le G Eq (fun _ _ h => h.symm) 1 Δ (by norm_num) hΔ (by
      intro u v
      convert hrel₁ u v using 0
      congr!) hdeg m hm
    have hb := hrot.trans (mul_le_mul_of_nonneg_left hanch (by positivity))
    apply le_trans _ hrep
    dsimp only [bad₁, T, T', Δ, A, m] at hb ⊢
    convert hb using 0
    congr!
  have hS₂ : (∑ x, if bad₂ x then cycW A x else 0) ≤ T / 4 := by
    have hrot := bad2_le_rot A (adjR_nonneg G) r m hm
    have hanch := conflict2_le G r hr (B / (s - 1)) Δ (by dsimp [B]; positivity) hΔ (by
      intro b e he
      convert hrel b e he using 0
      congr!) hdeg m hm
    have hb := hrot.trans (mul_le_mul_of_nonneg_left hanch (by positivity))
    apply le_trans _ hcodeg
    dsimp only [bad₂, two, T, T', B, s, Δ, A, m] at hb ⊢
    convert hb using 0
    congr!
  let cycle (x : Fin (2 * m) → Fin n) := ∀ i, G.Adj (x i) (x (nxt i))
  let small (x : Fin (2 * m) → Fin n) := ∀ i,
    (#(G.neighborFinset (x i) ∩ G.neighborFinset (x (two i))) : ℝ) ≤ s
  let C := univ.filter fun x : Fin (2 * m) → Fin n => Function.Injective x ∧ cycle x ∧ small x
  have hC (x) (hx : x ∈ C) : Function.Injective x ∧ cycle x ∧ small x := (mem_filter.mp hx).2
  have hpoint (x : Fin (2 * m) → Fin n) : cycW A x - (if bad₁ x then cycW A x else 0) -
      (if bad₂ x then cycW A x else 0) ≤ if x ∈ C then (1 : ℝ) else 0 := by
    have hw : cycW A x = if cycle x then 1 else 0 := cycW_adjR G x
    by_cases hcyc : cycle x
    · rw [if_pos hcyc] at hw
      rw [hw]
      by_cases h₁ : bad₁ x
      · split_ifs <;> norm_num
      by_cases h₂ : bad₂ x
      · split_ifs <;> norm_num
      have hinj : Function.Injective x := fun i j hij =>
        by_contra fun hne => h₁ ⟨i, j, hne, hij⟩
      have hx : x ∈ C := by
        apply mem_filter.mpr
        refine ⟨mem_univ _, hinj, hcyc, fun i => le_of_not_gt fun hgt => h₂ ⟨i, ?_, hgt⟩⟩
        exact fun h => diff14 hL i (hinj h)
      simp [h₁, h₂, hx]
    · rw [if_neg hcyc] at hw
      rw [hw]
      split_ifs <;> norm_num
  have hsum := Finset.sum_le_sum (s := univ) (fun x _ => hpoint x)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, total_cycW_eq_trace A m hm] at hsum
  have hcard : T - (∑ x, if bad₁ x then cycW A x else 0) -
      (∑ x, if bad₂ x then cycW A x else 0) ≤ (#C : ℝ) := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsum
    dsimp only [T]
    convert hsum using 0
    congr!
  have hhalf : T / 2 ≤ (#C : ℝ) := by linarith only [hcard, hS₁, hS₂]
  have hCpos : 0 < (#C : ℝ) := lt_of_lt_of_le (by linarith only [hpos]) hhalf
  refine ⟨C, Finset.card_pos.mp (by exact_mod_cast hCpos), s, hs,
    fun x hx => ⟨(hC x hx).1, (hC x hx).2.1⟩,
    fix1_card G (2 * m) hL s C (fun x hx => (hC x hx).2), fun i => ?_⟩
  obtain ⟨P, hP, hP'⟩ := forget2_card G Δ hΔ hdeg (2 * m) hL C (fun x hx => (hC x hx).2.1) i
  refine ⟨P, hP.trans (hlast.trans ?_), hP'⟩
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf (by positivity)) (by positivity)
