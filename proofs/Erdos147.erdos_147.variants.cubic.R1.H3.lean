import OMAReductions.R_Erdos147_erdos_147_variants_cubic_R1

/-!
# Étape `H3` de la réduction R1 d'Erdős 147 (variante cubique)

Lemme 2.5 de Janzer (arXiv 2109.06110) sous forme asymptotique, par une preuve pondérée par
la marche aléatoire simple : cycles homomorphes de poids `∏ P(x_i, x_(i+1))`, `P = D⁻¹A`.
-/

-- Credit: @iLc0

open SimpleGraph Finset Filter Asymptotics Matrix
open scoped Classical

namespace E147H3

/-- Matrice de la marche aléatoire simple : `walkM G u v = 1 / d(u)` si `u ~ v`, `0` sinon. -/
noncomputable def walkM {W : Type} [Fintype W] (G : SimpleGraph W) : Matrix W W ℝ :=
  fun u v => if G.Adj u v then ((G.degree u : ℝ))⁻¹ else 0

/-- Poids d'un uplet cyclique `x : Fin L → W` : produit des `M (x i) (x (i+1 mod L))`. -/
noncomputable def cycW {W : Type} [Fintype W] (M : Matrix W W ℝ) {L : ℕ} (x : Fin L → W) : ℝ :=
  ∏ i : Fin L, M (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ i.pos⟩)

-- Lemme 9 : découpe des uplets cycliques, borne de Cauchy–Schwarz pondérée.

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

private theorem trip9 {W : Type} [Fintype W] (M : Matrix W W ℝ) (k : ℕ) (hk : 2 ≤ k)
    (F : W → W → W → ℝ) :
    ∑ x : Fin (2*k) → W, cycW M x * F (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) =
    ∑ a, ∑ b, ∑ c, M a b * (M^k) b c * (M^(k-1)) c a * F a b c := by
  classical
  rw [cyc_split M k 1 hk (by omega) (by omega) (fun a b _ c => F a b c)]
  simp [Matrix.one_apply, mul_ite, ite_mul, sum_ite_irrel]

private theorem nn9 {W : Type} [Fintype W] (G : SimpleGraph W) (a b : W) :
    0 ≤ walkM G a b := by unfold walkM; split <;> positivity

private theorem row9 {W : Type} [Fintype W] (G : SimpleGraph W) (a : W) :
    ∑ b, walkM G a b ≤ 1 := by
  classical
  simp only [walkM, ← sum_filter, sum_const, nsmul_eq_mul, ← G.neighborFinset_eq_filter,
    G.card_neighborFinset_eq_degree]
  by_cases h : (G.degree a : ℝ) = 0 <;> simp [h]

private theorem iso9 {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ) (hm : 0 < m)
    (a b : W) (ha : G.degree a = 0) : (walkM G ^ m) a b = 0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [pow_succ', Matrix.mul_apply]
  simp [walkM, ha]

private theorem trace9 {W : Type} [Fintype W] (M : Matrix W W ℝ) (p q : ℕ) :
    trace (M ^ (p+q)) = ∑ a, ∑ b, (M^p) a b * (M^q) b a := by
  simp only [pow_add, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem ratio9 {U V : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V) : V * (U / V) ≤ U := by
  by_cases h : V = 0
  · simp [h, hU]
  · exact le_of_eq (by field_simp)

private theorem upperFirst9 {W : Type} [Fintype W] (G : SimpleGraph W) (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2*k) → W, cycW (walkM G) x *
      (((walkM G)^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) /
       ((walkM G)^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩)) ≤
    trace (walkM G ^ (2*(k-1))) := by
  classical
  let M := walkM G
  let P := fun n : ℕ => M^n
  have hn := Matrix.pow_apply_nonneg (nn9 G)
  rw [trip9 (walkM G) k hk (fun a b c => (P (k-1)) a c / (P k) b c),
    two_mul, trace9]
  apply sum_le_sum
  intro a _
  rw [sum_comm]
  apply sum_le_sum
  intro c _
  calc
    _ ≤ ∑ b, M a b * ((P (k-1)) a c * (P (k-1)) c a) := by
      apply sum_le_sum
      intro b _
      have hh := mul_le_mul_of_nonneg_left (ratio9 (hn (k-1) a c) (hn k b c))
        (mul_nonneg (nn9 G a b) (hn (k-1) c a))
      dsimp [M, P] at *
      linarith only [hh]
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_of_le_one_left (mul_nonneg (hn _ _ _) (hn _ _ _)) (row9 G a)

private theorem mass9 {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (α : ℝ)
    (hrel : ∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤ α * G.degree v)
    (n : ℕ) (hn : 0 < n)
    (hrev : ∀ a c, (G.degree a : ℝ) * (walkM G^n) a c = G.degree c * (walkM G^n) c a)
    (b e c : W) :
    ∑ a, (if r a e then walkM G a b * (walkM G^n) c a / (walkM G^n) a c else 0) ≤
      α * G.degree b / G.degree c := by
  classical
  calc
    _ ≤ ∑ a, (if G.Adj b a ∧ r e a then (1 : ℝ) else 0) / G.degree c := by
      apply sum_le_sum
      intro a _
      by_cases h : r a e
      · rw [if_pos h]
        by_cases hab : G.Adj a b
        · rw [if_pos ⟨hab.symm, hr _ _ h⟩]
          simp only [walkM, if_pos hab]
          by_cases hc : G.degree c = 0
          · simp [hc, iso9 G n hn c a hc]
          by_cases hp : (walkM G^n) a c = 0
          · rw [hp]
            simp
          have ha : (G.degree a : ℝ) ≠ 0 := by exact_mod_cast hab.degree_pos_left.ne'
          have hc' : (G.degree c : ℝ) ≠ 0 := by exact_mod_cast hc
          change (G.degree a : ℝ)⁻¹ * (walkM G^n) c a / (walkM G^n) a c ≤ _
          apply le_of_eq
          field_simp [ha,hc',hp]
          linarith only [hrev a c]
        · have hba : ¬ G.Adj b a := fun h => hab h.symm
          simp [walkM, hab, hba]
      · simp only [if_neg h]
        positivity
    _ = (#((G.neighborFinset b).filter (r e)) : ℝ) / G.degree c := by
      rw [← sum_div, sum_boole]
      have hs : univ.filter (fun a => G.Adj b a ∧ r e a) = (G.neighborFinset b).filter (r e) := by
        ext a
        simp
      rw [hs]
    _ ≤ _ := div_le_div_of_nonneg_right (hrel e b) (by positivity)

private theorem upperOne9 {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (α : ℝ) (hα : 0 ≤ α)
    (hrel : ∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤ α * G.degree v)
    (hrev : ∀ (m : ℕ) (u v : W),
      (G.degree u : ℝ) * (walkM G ^ m) u v = G.degree v * (walkM G ^ m) v u)
    (k j : ℕ) (hk : 2 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∑ x : Fin (2*k) → W, cycW (walkM G) x *
      (if r (x ⟨0,by omega⟩) (x ⟨j,by omega⟩) then
       ((walkM G)^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) /
       ((walkM G)^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) else 0) ≤
    α * trace (walkM G ^ (2*k)) := by
  classical
  let M := walkM G
  let P := fun n : ℕ => M^n
  let D := fun a : W => (G.degree a : ℝ)
  have hn := Matrix.pow_apply_nonneg (nn9 G)
  rw [cyc_split (walkM G) k j hk hj hjk
    (fun a b e c => if r a e then (P k) b c / (P (k-1)) a c else 0),
    two_mul, trace9, mul_sum]
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
  have hc : D b * (P k) b c / D c ≤ (P k) c b := by
    by_cases hd : D c = 0
    · simpa [hd] using hn k c b
    · apply le_of_eq
      apply (div_eq_iff hd).mpr
      simpa [D, P, M, mul_comm] using hrev k b c
  calc
    _ ≤ ∑ e, (α * D b / D c) * ((P (j-1)) b e * (P (k+1-j)) e c * (P k) b c) := by
      apply sum_le_sum
      intro e _
      have hh := mass9 G r hr α hrel (k-1) (by omega) (hrev _) b e c
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hh
        (mul_nonneg (mul_nonneg (hn _ _ _) (hn _ _ _)) (hn _ _ _)))
      rw [sum_mul]
      apply sum_congr rfl
      intro a _
      dsimp [f, P, M]
      by_cases hr' : r a e <;> simp [hr']
      ring
    _ = α * (P k) b c * (D b * (P k) b c / D c) := by
      rw [← mul_sum, ← sum_mul]
      have hp : (∑ e, (P (j-1)) b e * (P (k+1-j)) e c) = (P k) b c := by
        change ((M^(j-1)) * (M^(k+1-j))) b c = _
        rw [← pow_add, show j-1 + (k+1-j) = k by omega]
      rw [hp]
      ring
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hc (mul_nonneg hα (hn _ _ _))

private theorem cw9_nonneg {W : Type} [Fintype W] (G : SimpleGraph W) {N : ℕ}
    (x : Fin N → W) : 0 ≤ cycW (walkM G) x :=
  prod_nonneg (fun _ _ => nn9 G _ _)

private theorem support9 {W : Type} [Fintype W] (G : SimpleGraph W)
    (hrev : ∀ (m : ℕ) (u v : W),
      (G.degree u : ℝ) * (walkM G ^ m) u v = G.degree v * (walkM G ^ m) v u)
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (2*k) → W) (hx : cycW (walkM G) x ≠ 0) :
    (walkM G^(k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 ∧
    (walkM G^k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) ≠ 0 := by
  classical
  let M := walkM G
  let P := fun n : ℕ => M^n
  let bad := fun a b c : W => if (P (k-1)) a c = 0 ∨ (P k) b c = 0 then (1:ℝ) else 0
  let term := fun y : Fin (2*k) → W => cycW M y * bad (y ⟨0,by omega⟩) (y ⟨1,by omega⟩)
    (y ⟨k+1,by omega⟩)
  have hzero : ∑ y, term y = 0 := by
    dsimp only [term]
    rw [trip9 M k hk bad]
    apply sum_eq_zero
    intro a _
    apply sum_eq_zero
    intro b _
    apply sum_eq_zero
    intro c _
    by_cases ha : (P (k-1)) a c = 0
    · have hc : (P (k-1)) c a = 0 := by
        by_cases hd : G.degree c = 0
        · exact iso9 G _ (by omega) c a hd
        · have hh := hrev (k-1) a c
          change _ * (P (k-1)) a c = _ * (P (k-1)) c a at hh
          rw [ha, mul_zero] at hh
          exact (mul_eq_zero.mp hh.symm).resolve_left (by exact_mod_cast hd)
      change _ * (P (k-1)) c a * _ = 0
      simp [hc]
    · by_cases hb : (P k) b c = 0
      · change _ * (P k) b c * _ * _ = 0
        simp [hb]
      · simp [bad, ha, hb]
  have hn (y) (_ : y ∈ univ) : 0 ≤ term y := by
    dsimp only [term,bad]
    exact mul_nonneg (cw9_nonneg G y) (by split <;> norm_num)
  have hh := (sum_eq_zero_iff_of_nonneg hn).mp hzero x (mem_univ x)
  dsimp only [term,bad] at hh
  by_contra! h
  have h' : (P (k-1)) (x ⟨0,by omega⟩) (x ⟨k+1,by omega⟩) = 0 ∨
      (P k) (x ⟨1,by omega⟩) (x ⟨k+1,by omega⟩) = 0 := by tauto
  rw [if_pos h', mul_one] at hh
  exact hx hh

/-- Poids des uplets cycliques en conflit depuis la position 0 (lemme clé de Janzer [Ja20],
version pondérée par la marche aléatoire). -/
theorem conflict0_le {W : Type} [Fintype W] (G : SimpleGraph W) (r : W → W → Prop)
    (hr : ∀ u w, r u w → r w u) (α : ℝ) (hα : 0 ≤ α)
    (hrel : ∀ u v, (#((G.neighborFinset v).filter (r u)) : ℝ) ≤ α * G.degree v)
    (hrev : ∀ (m : ℕ) (u v : W),
      (G.degree u : ℝ) * (walkM G ^ m) u v = G.degree v * (walkM G ^ m) v u)
    (k : ℕ) (hk : 2 ≤ k) :
    ∑ x : Fin (2 * k) → W,
        (if ∃ j : Fin (2 * k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (x ⟨0, by omega⟩) (x j)
          then cycW (walkM G) x else 0) ≤
      Real.sqrt (k * α * trace (walkM G ^ (2 * (k - 1))) * trace (walkM G ^ (2 * k))) := by
  classical
  let X := Fin (2*k) → W
  let M := walkM G
  let P := fun n : ℕ => M^n
  let a := fun x : X => x ⟨0,by omega⟩
  let b := fun x : X => x ⟨1,by omega⟩
  let c := fun x : X => x ⟨k+1,by omega⟩
  let hit := fun x : X =>
    ∃ j : Fin (2*k), 1 ≤ j.val ∧ j.val ≤ k ∧ r (a x) (x j)
  let T := fun x : X => if hit x then cycW M x else 0
  let A := fun x : X => (P (k-1)) (a x) (c x)
  let B := fun x : X => (P k) (b x) (c x)
  have hn := Matrix.pow_apply_nonneg (nn9 G)
  have hA (x : X) : 0 ≤ A x := hn _ _ _
  have hB (x : X) : 0 ≤ B x := hn _ _ _
  have hT (x : X) : 0 ≤ T x := by
    dsimp only [T]
    split
    · exact cw9_nonneg G x
    · rfl
  have hf (x : X) : 0 ≤ T x * (A x / B x) := mul_nonneg (hT x) (div_nonneg (hA x) (hB x))
  have hg (x : X) : 0 ≤ T x * (B x / A x) := mul_nonneg (hT x) (div_nonneg (hB x) (hA x))
  have cs := sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset X)
    (fun x _ => hf x) (fun x _ => hg x) (r := T) (by
      intro x _
      by_cases h : cycW M x = 0
      · simp [T,h]
      · obtain ⟨h₁,h₂⟩ := support9 G hrev k hk x h
        have h₁' : A x ≠ 0 := h₁
        have h₂' : B x ≠ 0 := h₂
        apply le_of_eq
        field_simp [h₁',h₂'])
  have hfirst : ∑ x, T x * (A x / B x) ≤ trace (P (2*(k-1))) := by
    apply le_trans _ (upperFirst9 G k hk)
    apply sum_le_sum
    intro x _
    change T x * (A x / B x) ≤ cycW M x * (A x / B x)
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (hA x) (hB x))
    dsimp only [T]
    split
    · rfl
    · exact cw9_nonneg G x
  let idx := fun p : Fin k => (⟨p.val+1,by omega⟩ : Fin (2*k))
  let term := fun (x : X) (p : Fin k) =>
    cycW M x * (if r (a x) (x (idx p)) then B x / A x else 0)
  have hterm (x p) : 0 ≤ term x p := by
    apply mul_nonneg (cw9_nonneg G x)
    split
    · exact div_nonneg (hB x) (hA x)
    · rfl
  have hsecond : ∑ x, T x * (B x / A x) ≤ (k:ℝ) * (α * trace (P (2*k))) := by
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
      _ ≤ ∑ _p : Fin k, α * trace (P (2*k)) := by
        apply sum_le_sum
        intro p _
        exact upperOne9 G r hr α hα hrel hrev k (p.val+1) hk (by omega) (by omega)
      _ = _ := by simp [nsmul_eq_mul]
  apply Real.le_sqrt_of_sq_le
  change (∑ x, T x)^2 ≤ _
  calc
    _ ≤ _ := cs
    _ ≤ _ := mul_le_mul hfirst hsecond (sum_nonneg (fun x _ => hg x))
      (le_trans (sum_nonneg (fun x _ => hf x)) hfirst)
    _ = _ := by dsimp [P,M]; ring

-- Lemme 10 : réversibilité, traces paires, rotations.

theorem walkM_nonneg {W : Type} [Fintype W] (G : SimpleGraph W) (u v : W) :
    0 ≤ walkM G u v := by
  unfold walkM
  split <;> positivity

theorem walkM_pow_nonneg {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ) (u v : W) :
    0 ≤ (walkM G ^ m) u v := by
  induction m generalizing u v with
  | zero => simp only [pow_zero, Matrix.one_apply]; split <;> norm_num
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact sum_nonneg fun _ _ ↦ mul_nonneg (ih ..) (walkM_nonneg ..)

private theorem walkM_balance {W : Type} [Fintype W] (G : SimpleGraph W) (w : W → ℝ)
    (hw : ∀ u, 0 < G.degree u → w u = G.degree u) (m : ℕ) (u v : W) :
    w u * (walkM G ^ m) u v = w v * (walkM G ^ m) v u := by
  have base (a b : W) : w a * walkM G a b = w b * walkM G b a := by
    by_cases h : G.Adj a b
    · simp [walkM, h, h.symm, hw a h.degree_pos_left, hw b h.degree_pos_right,
          h.degree_pos_left.ne', h.degree_pos_right.ne']
    · have h' : ¬G.Adj b a := fun e ↦ h e.symm
      simp [walkM, h, h']
  induction m generalizing u v with
  | zero =>
    by_cases h : u = v <;> simp [h, Ne.symm]
  | succ m ih =>
    conv_lhs => rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
    conv_rhs => rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    apply sum_congr rfl
    intro z _
    linear_combination (walkM G ^ m) z v * base u z + walkM G z u * ih z v

/-- Réversibilité de la marche aléatoire : `d(u) Pᵐ(u,v) = d(v) Pᵐ(v,u)`. -/
theorem walkM_pow_rev {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ) (u v : W) :
    (G.degree u : ℝ) * (walkM G ^ m) u v = G.degree v * (walkM G ^ m) v u := by
  exact walkM_balance G _ (fun _ _ ↦ rfl) m u v

private theorem trace_split_walkM {W : Type} [Fintype W] (G : SimpleGraph W) (a b : ℕ) :
    trace (walkM G ^ (a + b)) = ∑ p : W × W, (walkM G ^ a) p.1 p.2 * (walkM G ^ b) p.2 p.1 := by
  simp [pow_add, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Log-convexité des traces paires. -/
theorem trace_walkM_logconvex {W : Type} [Fintype W] (G : SimpleGraph W) (j : ℕ) (hj : 1 ≤ j) :
    trace (walkM G ^ (2 * j)) ^ 2 ≤
      trace (walkM G ^ (2 * (j - 1))) * trace (walkM G ^ (2 * (j + 1))) := by
  let w (u : W) : ℝ := if G.degree u = 0 then 1 else G.degree u
  have hw (u : W) (hu : 0 < G.degree u) : w u = G.degree u := by simp [w, hu.ne']
  have hw' (u : W) : w u ≠ 0 := by unfold w; split <;> simp_all
  let a := j - 1
  let b := j + 1
  rw [show 2 * j = a + b by dsimp [a, b]; omega, trace_split_walkM,
      show 2 * (j - 1) = a + a by dsimp [a]; omega, trace_split_walkM,
      show 2 * (j + 1) = b + b by dsimp [b]; omega, trace_split_walkM]
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun _ _ ↦ mul_nonneg (walkM_pow_nonneg ..) (walkM_pow_nonneg ..)
  · exact fun _ _ ↦ mul_nonneg (walkM_pow_nonneg ..) (walkM_pow_nonneg ..)
  · rintro ⟨u, v⟩ _
    dsimp only
    have he : (walkM G ^ a) u v * (walkM G ^ b) v u =
        (walkM G ^ a) v u * (walkM G ^ b) u v := by
      apply mul_left_cancel₀ (hw' u)
      linear_combination (walkM G ^ b) v u * walkM_balance G w hw a u v -
          (walkM G ^ a) v u * walkM_balance G w hw b u v
    apply le_of_eq
    linear_combination (walkM G ^ a) u v * (walkM G ^ b) v u * he

private theorem walkM_row {W : Type} [Fintype W] (G : SimpleGraph W) (m : ℕ)
    (u : W) (hu : 0 < G.degree u) : ∑ v, (walkM G ^ m) u v = 1 := by
  have row (z : W) (hz : 0 < G.degree z) : ∑ v, walkM G z v = 1 := by
    simp only [walkM, ← Finset.sum_filter, ← G.neighborFinset_eq_filter,
      sum_const, card_neighborFinset_eq_degree, nsmul_eq_mul]
    simp [hz.ne']
  induction m generalizing u with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
    simp only [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← row u hu]
    apply sum_congr rfl
    intro z _
    by_cases h : G.Adj u z
    · rw [ih z h.degree_pos_right, mul_one]
    · simp [walkM, h]

theorem one_le_trace_walkM {W : Type} [Fintype W] (G : SimpleGraph W)
    (hG : G.edgeFinset.Nonempty) (k : ℕ) : 1 ≤ trace (walkM G ^ (2 * k)) := by
  let d (u : W) : ℝ := G.degree u
  let P := walkM G ^ k
  have hsum : ∑ p : W × W, d p.1 * P p.1 p.2 = ∑ u, d u := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro u _
    change (∑ v, d u * P u v) = d u
    rw [← Finset.mul_sum]
    by_cases hu : 0 < G.degree u
    · rw [show ∑ v, P u v = 1 from walkM_row G k u hu, mul_one]
    · simp [d, Nat.eq_zero_of_not_pos hu]
  have hsq : ∑ p : W × W, d p.1 * d p.2 = (∑ u, d u) ^ 2 := by
    rw [Fintype.sum_prod_type, sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hpos : 0 < ∑ u, d u := by
    have h : 0 < ∑ u, G.degree u := by
      rw [G.sum_degrees_eq_twice_card_edges]; exact Nat.mul_pos (by decide) (card_pos.mpr hG)
    dsimp [d]
    exact_mod_cast h
  have hc : (∑ p : W × W, d p.1 * P p.1 p.2) ^ 2 ≤
      (∑ p : W × W, P p.1 p.2 * P p.2 p.1) * ∑ p : W × W, d p.1 * d p.2 := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · exact fun _ _ ↦ mul_nonneg (walkM_pow_nonneg ..) (walkM_pow_nonneg ..)
    · intro i _; dsimp [d]; positivity
    · rintro ⟨u, v⟩ _
      apply le_of_eq
      dsimp [d, P]
      linear_combination (G.degree u : ℝ) * (walkM G ^ k) u v * walkM_pow_rev G k u v
  rw [hsum, hsq, ← trace_split_walkM G k k] at hc
  rw [two_mul]
  exact le_of_mul_le_mul_right (by simpa only [one_mul] using hc :
    1 * (∑ u, d u) ^ 2 ≤ _ * _) (sq_pos_of_pos hpos)

theorem trace_walkM_interp {W : Type} [Fintype W] (G : SimpleGraph W)
    (hG : G.edgeFinset.Nonempty) (k : ℕ) (hk : 1 ≤ k) :
    trace (walkM G ^ (2 * (k - 1))) ≤
      (Fintype.card W : ℝ) ^ (1 / (k : ℝ)) * trace (walkM G ^ (2 * k)) ^ (1 - 1 / (k : ℝ)) := by
  let T (n : ℕ) := trace (walkM G ^ (2 * n))
  have pos (n : ℕ) : 0 < T n := lt_of_lt_of_le zero_lt_one (one_le_trace_walkM G hG n)
  let a (n : ℕ) := Real.log (T n)
  have step (n : ℕ) : a (n + 1) - a n ≤ a (n + 2) - a (n + 1) := by
    have h : T (n + 1) ^ 2 ≤ T n * T (n + 2) := by
      simpa [T] using trace_walkM_logconvex G (n + 1) (by omega)
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

end E147H3

open E147H3 in
private theorem total_cycW_eq_trace {W : Type} [Fintype W] (M : Matrix W W ℝ)
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

private theorem strict_conflict_bound {n k θ p t : ℝ} (hn : 0 < n) (hk : 0 < k)
    (ht : 1 ≤ t) (hp : p ≤ n ^ (1 / k) * t ^ (1 - 1 / k))
    (hbig : 4 * k ^ 3 < n ^ θ) :
    2 * k * Real.sqrt (k * n ^ (-(1 / k + θ)) * p * t) < t := by
  have ht' : 0 < t := zero_lt_one.trans_le ht
  have h2k : 0 < 2 * k := by positivity
  have hp' : p ≤ n ^ (1 / k) * t := hp.trans (mul_le_mul_of_nonneg_left
    (calc
      t ^ (1 - 1 / k) ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht (by
        have : 0 ≤ 1 / k := by positivity
        linarith)
      _ = t := Real.rpow_one _) (Real.rpow_nonneg hn.le _))
  have hexp : n ^ (-(1 / k + θ)) * n ^ (1 / k) = (n ^ θ)⁻¹ := by
    rw [← Real.rpow_add hn, show -(1 / k + θ) + 1 / k = -θ by ring, Real.rpow_neg hn.le]
  have hfac : 4 * k ^ 3 * (n ^ θ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hn _)]
    exact hbig
  rw [mul_comm (2 * k), ← lt_div_iff₀ h2k, Real.sqrt_lt' (div_pos ht' h2k), div_pow,
    lt_div_iff₀ (sq_pos_of_pos h2k)]
  calc
    _ ≤ k * n ^ (-(1 / k + θ)) * (n ^ (1 / k) * t) * t * (2 * k) ^ 2 := by
      gcongr
    _ = (4 * k ^ 3 * (n ^ (-(1 / k + θ)) * n ^ (1 / k))) * t ^ 2 := by ring
    _ < t ^ 2 := by
      rw [hexp]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hfac (sq_pos_of_pos ht')

open E147H3 in
theorem OMA.solution : OMA.R_Erdos147_erdos_147_variants_cubic_R1.H3 := by
  classical
  intro k hk θ hθ
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_gt_atTop (4 * (k : ℝ) ^ 3)]
    with N hN hbig
  intro W _ hW G r hr hG hrel
  let M := walkM G
  let bad (x : Fin (2 * k) → W) := ∃ i j, i ≠ j ∧ r (x i) (x j)
  have ht := one_le_trace_walkM G hG k
  have hp := trace_walkM_interp G hG k (by omega)
  rw [hW] at hp
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc := conflict0_le G r hr _ (Real.rpow_nonneg hN'.le _) hrel (walkM_pow_rev G) k hk
  have hbad : (∑ x : Fin (2 * k) → W, if bad x then cycW M x else 0) <
      trace (M ^ (2 * k)) :=
    (bad_le_rot M (walkM_nonneg G) r hr k hk).trans_lt
      ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_lt
        (strict_conflict_bound hN' hk' ht hp hbig))
  obtain ⟨x, hx, hb⟩ : ∃ x : Fin (2 * k) → W, cycW M x ≠ 0 ∧ ¬ bad x := by
    by_contra h
    apply (not_le_of_gt hbad)
    rw [← total_cycW_eq_trace M k hk]
    apply Finset.sum_le_sum
    intro x _
    split_ifs with hb
    · exact le_rfl
    · by_cases hw : cycW M x = 0
      · rw [hw]
      · exact (h ⟨x, hw, hb⟩).elim
  refine ⟨x, ?_, fun i j hij hr' => hb ⟨i, j, hij, hr'⟩⟩
  intro i
  by_contra hadj
  apply hx
  unfold cycW
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [M, walkM, hadj])
