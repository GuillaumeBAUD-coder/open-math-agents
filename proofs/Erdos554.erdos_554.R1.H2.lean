import OMAReductions.R_Erdos554_erdos_554_R1

/-! Derived from @iLc0’s accepted ACJMR proof in this repository at 6485bff6143494026930aa6314111c4a291b6ad4. The final estimate absorbs the additive constant. -/
/-!
# ACJMR : R_k(C_{2n+1}) ≤ (4n-2)^k k^{k/n} + 1

Lemme 2.1 d'Axenovich, Cames van Batenburg, Janzer, Michel et Rundström (argument de poids), et la
borne d'Erdős, Faudree, Rousseau et Schelp (couches de nombre chromatique au plus 2ℓ-1),
reconstruite par un ordre de parcours en profondeur et l'argument de Gallai–Roy.
-/

open SimpleGraph Finset

namespace OMA554A

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Boule de rayon `d` autour de `v` dans `U` pour la relation `R` (voisinages itérés). -/
noncomputable def ball (R : V → V → Prop) (U : Finset V) (v : V) : ℕ → Finset V
  | 0 => {v}
  | d + 1 => ball R U v d ∪ U.filter (fun y => ∃ x ∈ ball R U v d, R x y)

section

omit [Fintype V]

private theorem wb_mono (A : V → V → Prop) (U : Finset V) (v : V) :
    Monotone (ball A U v) := by
  apply monotone_nat_of_le_succ
  intro i
  exact subset_union_left

private theorem wb_root (A : V → V → Prop) (U : Finset V) (v : V) (i : ℕ) :
    v ∈ ball A U v i :=
  wb_mono A U v (Nat.zero_le i) (by simp [ball])

private theorem wb_sub (A : V → V → Prop) {U : Finset V} {v : V} (hv : v ∈ U) (i : ℕ) :
    ball A U v i ⊆ U := by
  induction i with
  | zero => simpa [ball]
  | succ i ih => exact union_subset ih (filter_subset _ _)

private theorem wb_next {A : V → V → Prop} {U : Finset V} {v x y : V} {i : ℕ}
    (hx : x ∈ ball A U v i) (hy : y ∈ U) (h : A x y) : y ∈ ball A U v (i + 1) :=
  mem_union_right _ (mem_filter.mpr ⟨hy, x, hx, h⟩)

private theorem wb_prev {A : V → V → Prop} {U : Finset V} {v x : V} (hv : v ∈ U)
    (hxv : x ≠ v) {i : ℕ} (hx : x ∈ ball A U v i) : ∃ y ∈ U, A y x := by
  induction i with
  | zero => simp [ball, hxv] at hx
  | succ i ih =>
    rcases mem_union.mp hx with h | h
    · exact ih h
    · obtain ⟨_, y, hy, h⟩ := mem_filter.mp h
      exact ⟨y, wb_sub A hv i hy, h⟩

omit [DecidableEq V] in
/-- Une fibre porte au moins le poids moyen. -/
private theorem w_fibre {m : ℕ} (hm : 1 ≤ m) (S : Finset V) (f : V → Fin m) (w : V → ℝ) :
    ∃ a, (∑ x ∈ S, w x) ≤ (m : ℝ) * ∑ x ∈ S.filter (fun x => f x = a), w x := by
  classical
  let F (a : Fin m) := ∑ x ∈ S.filter (fun x => f x = a), w x
  obtain ⟨a, _, ha⟩ := univ.exists_max_image F ⟨⟨0, by omega⟩, mem_univ _⟩
  refine ⟨a, ?_⟩
  calc
    _ = ∑ b, F b := (sum_fiberwise_of_maps_to (fun x (_ : x ∈ S) => mem_univ (f x)) w).symm
    _ ≤ ∑ _b : Fin m, F a := sum_le_sum ha
    _ = _ := by simp [F, nsmul_eq_mul]

omit [DecidableEq V] in
private theorem w_mono_sum (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) {S T : Finset V} (h : S ⊆ T) :
    (∑ x ∈ S, w x) ≤ ∑ x ∈ T, w x :=
  sum_le_sum_of_subset_of_nonneg h fun x _ _ => hw x

/-- La boule de rayon un d'une couleur incidente porte une fraction au moins 1/k du poids. -/
private theorem w_first {k : ℕ} (R : Fin k → V → V → Prop)
    (hcov : ∀ x y, x ≠ y → ∃ c, R c x y) (hk : 1 ≤ k)
    {U : Finset V} {v z : V} (hv : v ∈ U) (hz : z ∈ U) (hvz : v ≠ z)
    (w : V → ℝ) (hw : ∀ x, 0 < w x) :
    ∃ c, (∃ u ∈ U, R c v u) ∧
      (∑ x ∈ U, w x) ≤ (k : ℝ) * ∑ x ∈ ball (R c) U v 1, w x := by
  classical
  obtain ⟨c₀, hc₀⟩ := hcov v z hvz
  let f (x : V) : Fin k := if h : v = x then c₀ else (hcov v x h).choose
  have hf {x : V} (h : v ≠ x) : R (f x) v x := by simpa [f, h] using (hcov v x h).choose_spec
  obtain ⟨c, hc⟩ := w_fibre hk U f w
  let S := U.filter (fun x => f x = c)
  have hne : S.Nonempty := by
    by_contra hn
    have h0 : S = ∅ := not_nonempty_iff_eq_empty.mp hn
    change (∑ x ∈ U, w x) ≤ (k : ℝ) * ∑ x ∈ S, w x at hc
    simp [h0] at hc
    exact (not_lt_of_ge hc) (sum_pos (fun x _ => hw x) ⟨v, hv⟩)
  obtain ⟨u, hu⟩ := hne
  obtain ⟨huU, huc⟩ := mem_filter.mp hu
  refine ⟨c, ?_, hc.trans (mul_le_mul_of_nonneg_left (w_mono_sum w (fun x => (hw x).le) ?_) (by positivity))⟩
  · by_cases h : v = u
    · have heq : c₀ = c := by simpa [f, h] using huc
      exact ⟨z, hz, heq ▸ hc₀⟩
    · exact ⟨u, huU, huc ▸ hf h⟩
  · intro x hx
    obtain ⟨hxU, hxc⟩ := mem_filter.mp hx
    by_cases h : v = x
    · exact h ▸ wb_root (R c) U v 1
    · exact wb_next (wb_root _ _ v 0) hxU (hxc ▸ hf h)

private theorem w_growth {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {t : ℝ} (ht : 0 ≤ t) (b : ℕ → ℝ)
    (hb : b (ℓ + 1) ≤ t ^ ℓ * b 1) :
    ∃ i, 1 ≤ i ∧ i ≤ ℓ ∧ b (i + 1) ≤ t * b i := by
  by_contra! h
  have H : ∀ j ≤ ℓ, t ^ j * b 1 ≤ b (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      calc
        _ = t * (t ^ j * b 1) := by rw [pow_succ]; ring
        _ ≤ t * b (j + 1) := mul_le_mul_of_nonneg_left (ih (by omega)) ht
        _ ≤ _ := (h (j+1) (by omega) hj).le
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show ℓ ≠ 0 by omega)
  have hle := mul_le_mul_of_nonneg_left (H j (by omega)) ht
  have hlt := h (j + 1) (by omega) le_rfl
  rw [pow_succ] at hb
  linarith only [hb, hle, hlt, show t ^ j * t * b 1 = t * (t ^ j * b 1) by ring]

end

/-- Couleurs absentes dans le sous-ensemble ; chacune donne un facteur de poids. -/
private noncomputable def w_absent {k : ℕ} (R : Fin k → V → V → Prop) (U : Finset V) (x : V) :
    Finset (Fin k) := univ.filter (fun c => ∀ y ∈ U, ¬ R c x y)

private theorem w_absent_anti {k : ℕ} (R : Fin k → V → V → Prop) {T U : Finset V}
    (h : T ⊆ U) (x : V) : w_absent R U x ⊆ w_absent R T x := by
  intro c hc
  exact mem_filter.mpr ⟨mem_univ _, fun y hy => (mem_filter.mp hc).2 y (h hy)⟩

/-- Le poids total normalisé par le nombre de couleurs absentes est borné par q^k. -/
private theorem w_total {k : ℕ} (R : Fin k → V → V → Prop)
    (hsymm : ∀ c x y, R c x y → R c y x)
    (hcov : ∀ x y, x ≠ y → ∃ c, R c x y)
    (χ ℓ : ℕ) (hχ : 1 ≤ χ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k)
    (hcol : ∀ (U : Finset V) (v : V), v ∈ U → ∀ (c : Fin k) (d : ℕ), 1 ≤ d → d ≤ ℓ →
      ∃ f : V → Fin χ, ∀ x ∈ ball (R c) U v d, ∀ y ∈ ball (R c) U v d, R c x y → f x ≠ f y)
    (t q : ℝ) (ht : 0 ≤ t) (htk : t ^ ℓ = k) (hq : 1 ≤ q) (hqeq : q = χ * t)
    (U : Finset V) : (∑ x ∈ U, q ^ (w_absent R U x).card) ≤ q ^ k := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    let W (A : Finset V) (x : V) := q ^ (w_absent R A x).card
    have hw (A : Finset V) (x : V) : 0 < W A x := pow_pos (by linarith) _
    by_cases hsmall : U.card ≤ 1
    · calc
        _ ≤ ∑ _x ∈ U, q ^ k := sum_le_sum fun x _ => pow_le_pow_right₀ hq (by
          simpa using (w_absent R U x).card_le_univ)
        _ = (U.card : ℝ) * q ^ k := by simp [nsmul_eq_mul]
        _ ≤ 1 * q ^ k := mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall) (by positivity)
        _ = _ := one_mul _
    obtain ⟨v, hv, z, hz, hvz⟩ := one_lt_card.mp (lt_of_not_ge hsmall)
    obtain ⟨c, ⟨u, hu, hru⟩, hfirst⟩ := w_first R hcov hk hv hz hvz (W U) (hw U)
    let B := ball (R c) U v
    let b (j : ℕ) := ∑ x ∈ B j, W U x
    have hlast : b (ℓ + 1) ≤ t ^ ℓ * b 1 := by
      rw [htk]
      exact (w_mono_sum _ (fun x => (hw U x).le) (wb_sub _ hv _)).trans hfirst
    obtain ⟨i, hi, hiℓ, hslow⟩ := w_growth hℓ ht b hlast
    obtain ⟨f, hf⟩ := hcol U v hv c i hi hiℓ
    obtain ⟨a, ha⟩ := w_fibre hχ (B i) f (W U)
    let S := (B i).filter (fun x => f x = a)
    let D := U \ B (i + 1)
    let T := D ∪ S
    have hSS : S ⊆ B i := filter_subset _ _
    have hBB : B i ⊆ B (i + 1) := wb_mono _ _ _ (by omega)
    have hBU (j : ℕ) : B j ⊆ U := wb_sub _ hv _
    have hTU : T ⊆ U := union_subset sdiff_subset (hSS.trans (hBU i))
    have hTB {x : V} (hx : x ∈ T) (hxb : x ∈ B (i + 1)) : x ∈ S := by
      rcases mem_union.mp hx with hd | hs
      · exact ((mem_sdiff.mp hd).2 hxb).elim
      · exact hs
    have hvB : v ∈ B i := wb_root _ _ _ _
    have huB : u ∈ B i := wb_mono _ _ _ hi (wb_next (wb_root _ _ _ 0) hu hru)
    have hproper : T ⊂ U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hTU, fun he => ?_⟩
      have hvS := hTB (he.symm ▸ hv) (hBB hvB)
      have huS := hTB (he.symm ▸ hu) (hBB huB)
      exact hf v hvB u huB hru ((mem_filter.mp hvS).2.trans (mem_filter.mp huS).2.symm)
    have hboost (x : V) (hx : x ∈ S) : q * W U x ≤ W T x := by
      have hcT : c ∈ w_absent R T x := by
        refine mem_filter.mpr ⟨mem_univ c, fun y hy hxy => ?_⟩
        have hyS := hTB hy (wb_next (hSS hx) (hTU hy) hxy)
        exact hf x (hSS hx) y (hSS hyS) hxy ((mem_filter.mp hx).2.trans (mem_filter.mp hyS).2.symm)
      have hcU : c ∉ w_absent R U x := by
        intro hc
        have hall := (mem_filter.mp hc).2
        by_cases hxv : x = v
        · exact hall u hu (hxv.symm ▸ hru)
        · obtain ⟨y, hy, hyx⟩ := wb_prev hv hxv (hSS hx)
          exact hall y hy (hsymm c y x hyx)
      have hlt := card_lt_card ((ssubset_iff_of_subset (w_absent_anti R hTU x)).mpr ⟨c, hcT, hcU⟩)
      calc
        _ = q ^ ((w_absent R U x).card + 1) := by simp [W, pow_succ, mul_comm]
        _ ≤ _ := pow_le_pow_right₀ hq hlt
    have hD : (∑ x ∈ D, W U x) ≤ ∑ x ∈ D, W T x :=
      sum_le_sum fun x _ => pow_le_pow_right₀ hq (card_le_card (w_absent_anti R hTU x))
    have hS : q * (∑ x ∈ S, W U x) ≤ ∑ x ∈ S, W T x := by
      rw [mul_sum]
      exact sum_le_sum hboost
    have hmass : b (i + 1) ≤ q * (∑ x ∈ S, W U x) := by
      rw [hqeq, mul_comm (χ : ℝ) t, mul_assoc]
      exact hslow.trans (mul_le_mul_of_nonneg_left ha ht)
    have hsplit : (∑ x ∈ D, W U x) + b (i + 1) = ∑ x ∈ U, W U x :=
      sum_sdiff (hBU _) 
    have hdis : Disjoint D S := disjoint_left.mpr fun x hxd hxs => (mem_sdiff.mp hxd).2 (hBB (hSS hxs))
    have hsplit' : (∑ x ∈ T, W T x) = (∑ x ∈ D, W T x) + ∑ x ∈ S, W T x := sum_union hdis
    change (∑ x ∈ U, W U x) ≤ _
    rw [← hsplit]
    exact ((add_le_add hD (hmass.trans hS)).trans_eq hsplit'.symm).trans (ih T hproper)

/-- Lemme 2.1 d'ACJMR. -/
theorem weight_lemma {k : ℕ} (R : Fin k → V → V → Prop)
    (hsymm : ∀ c x y, R c x y → R c y x) (hirr : ∀ c x, ¬ R c x x)
    (hcov : ∀ x y, x ≠ y → ∃ c, R c x y)
    (χ ℓ : ℕ) (hχ : 1 ≤ χ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k)
    (hcol : ∀ (U : Finset V) (v : V), v ∈ U → ∀ (c : Fin k) (d : ℕ), 1 ≤ d → d ≤ ℓ →
      ∃ f : V → Fin χ, ∀ x ∈ ball (R c) U v d, ∀ y ∈ ball (R c) U v d, R c x y → f x ≠ f y) :
    (Fintype.card V : ℝ) ≤ (χ : ℝ) ^ k * (k : ℝ) ^ ((k : ℝ) / ℓ) := by
  classical
  clear hirr
  let t : ℝ := (k : ℝ) ^ (1 / (ℓ : ℝ))
  let q : ℝ := (χ : ℝ) * t
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have ht : 1 ≤ t := Real.one_le_rpow hk' (by positivity)
  have hq : 1 ≤ q := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hχ) ht
  have htk : t ^ ℓ = k := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast (by positivity), one_div_mul_cancel hℓ'.ne', Real.rpow_one]
  have hbound := w_total R hsymm hcov χ ℓ hχ hℓ hk hcol t q (by linarith) htk hq rfl univ
  calc
    _ = ∑ _x : V, (1 : ℝ) := by simp
    _ ≤ _ := (sum_le_sum (fun (x : V) (_ : x ∈ univ) =>
      one_le_pow₀ hq (n := (w_absent R univ x).card))).trans hbound
    q ^ k = _ := by
      dsimp [q, t]
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
      congr 2
      ring

/-- Fenêtre : parmi `2ℓ - 1` hauteurs comprises entre 1 et ℓ, une fenêtre qui contient le maximum
a pour longueur exactement `2ℓ + 1 - 2·max`. -/
theorem window (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : ℕ → ℕ)
    (ha : ∀ r, r < 2 * ℓ - 1 → 1 ≤ a r ∧ a r ≤ ℓ) :
    ∃ s r t, s ≤ r ∧ r < t ∧ t ≤ 2 * ℓ - 1 ∧ t - s + 2 * a r = 2 * ℓ + 1 ∧
      ∀ r', s ≤ r' → r' < t → a r' ≤ a r := by
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image (Finset.range (2 * ℓ - 1)) a
    ⟨0, by rw [Finset.mem_range]; omega⟩
  rw [Finset.mem_range] at hr
  obtain ⟨h1, h2⟩ := ha r hr
  refine ⟨min r (2 * ℓ - 1 - (2 * ℓ + 1 - 2 * a r)), r,
    min r (2 * ℓ - 1 - (2 * ℓ + 1 - 2 * a r)) + (2 * ℓ + 1 - 2 * a r), ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · intro r' hr1 hr2
    exact hmax r' (Finset.mem_range.mpr (by omega))

private theorem cycle_of_indexed_loop (G : SimpleGraph V) (n : ℕ) (f : ℕ → V)
    (hclose : f n = f 0)
    (hstep : ∀ i, i < n → G.Adj (f i) (f (i+1)))
    (hdist : ∀ i j, i < j → j < n → f i ≠ f j) :
    cycleGraph n ⊑ G := by
  refine ⟨⟨⟨fun i ↦ f i.val, ?_⟩, ?_⟩⟩
  · have hdir (x y : Fin n) (h : (x - y).val = 1) : G.Adj (f y.val) (f x.val) := by
      by_cases hle : y ≤ x
      · rw [Fin.sub_val_of_le hle] at h
        have hx : x.val = y.val + 1 := by omega
        rw [hx]
        exact hstep _ y.isLt
      · have hlt : x < y := lt_of_not_ge hle
        rw [Fin.coe_sub_iff_lt.mpr hlt] at h
        have h₁ := x.isLt
        have h₂ := y.isLt
        have hx : x.val = 0 := by omega
        have hy : y.val + 1 = n := by omega
        have ha := hstep _ h₂
        rwa [hy, hclose, ← hx] at ha
    intro x y h
    rcases cycleGraph_adj'.mp h with h | h
    · exact (hdir x y h).symm
    · exact hdir y x h
  · intro i j he
    change f i.val = f j.val at he
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact (hdist _ _ h j.isLt he).elim
    · exact h
    · exact (hdist _ _ h i.isLt he.symm).elim

/-- Deux branches d'un arbre qui se séparent juste sous leur ancêtre commun, refermées par un
chemin de la couche `d`, donnent un cycle de longueur `2M + (t - s)`. -/
theorem cycle_of_branches (G : SimpleGraph V) (depth : V → ℕ) (par : V → V) (d : ℕ)
    (hpar : ∀ y, 1 ≤ depth y → depth y ≤ d → G.Adj (par y) y ∧ depth (par y) + 1 = depth y)
    (seq : ℕ → V) (s t : ℕ) (hst : s < t)
    (hdep : ∀ r, s ≤ r → r ≤ t → depth (seq r) = d)
    (hadj : ∀ r, s ≤ r → r < t → G.Adj (seq r) (seq (r + 1)))
    (hinj : ∀ r r', s ≤ r → r ≤ t → s ≤ r' → r' ≤ t → seq r = seq r' → r = r')
    (M : ℕ) (hM1 : 1 ≤ M) (hMd : M ≤ d)
    (hmeet : par^[M] (seq s) = par^[M] (seq t))
    (hsplit : par^[M - 1] (seq s) ≠ par^[M - 1] (seq t)) :
    cycleGraph (2 * M + (t - s)) ⊑ G := by
  let b := M + (t - s)
  let N := 2 * M + (t - s)
  have hb : M < b := by dsimp [b]; omega
  have hN : N = b + M := by dsimp [b, N]; omega
  have hbt : s + (b - M) = t := by dsimp [b]; omega
  have hs := hdep s le_rfl (by omega)
  have ht := hdep t (by omega) le_rfl
  have dep (x : V) (hx : depth x = d) (i : ℕ) (hi : i ≤ M) :
      depth (par^[i] x) + i = d := by
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      have h := ih (by omega)
      have hp := (hpar (par^[i] x) (by omega) (by omega)).2
      rw [Function.iterate_succ_apply']
      omega
  have step (x : V) (hx : depth x = d) (i : ℕ) (hi : i < M) :
      G.Adj (par^[i+1] x) (par^[i] x) := by
    have h := dep x hx i (by omega)
    rw [Function.iterate_succ_apply']
    exact (hpar _ (by omega) (by omega)).1
  have disj (k : ℕ) (hk : k < M) : par^[k] (seq s) ≠ par^[k] (seq t) := by
    intro he
    have he' := congrArg (par^[M - 1 - k]) he
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at he'
    exact hsplit (by simpa [show M - 1 - k + k = M - 1 by omega] using he')
  let f (i : ℕ) : V :=
    if i < M then par^[M-i] (seq s)
    else if i ≤ b then seq (s + (i-M)) else par^[i-b] (seq t)
  have leftSeg (i : ℕ) (hi : i ≤ M) : f i = par^[M-i] (seq s) := by
    rcases lt_or_eq_of_le hi with hi | rfl
    · simp [f, hi]
    · simp [f, hb.le]
  have midSeg (i : ℕ) (h₁ : M ≤ i) (h₂ : i ≤ b) : f i = seq (s + (i-M)) := by
    simp [f, not_lt.mpr h₁, h₂]
  have rightSeg (i : ℕ) (hi : b ≤ i) : f i = par^[i-b] (seq t) := by
    rcases lt_or_eq_of_le hi with hi | rfl
    · simp [f, show ¬i < M by omega, not_le.mpr hi]
    · simp [f, show ¬b < M by omega, hbt]
  have mdep (i : ℕ) (hi : M ≤ i) (hi' : i ≤ b) : depth (f i) = d := by
    rw [midSeg _ hi hi']
    exact hdep _ (by omega) (by omega)
  have ldep (i : ℕ) (hi : i ≤ M) : depth (f i) + (M-i) = d := by
    rw [leftSeg _ hi]
    exact dep _ hs _ (by omega)
  have rdep (i : ℕ) (hi : b ≤ i) (hi' : i ≤ N) : depth (f i) + (i-b) = d := by
    rw [rightSeg _ hi]
    exact dep _ ht _ (by omega)
  apply cycle_of_indexed_loop G N f
  · rw [rightSeg N (by omega), leftSeg 0 (by omega)]
    simpa [show N - b = M by omega] using hmeet.symm
  · intro i hi
    by_cases h₁ : i < M
    · rw [leftSeg i (by omega), leftSeg (i+1) (by omega)]
      have ha := step _ hs (M - (i+1)) (by omega)
      rwa [show M - (i+1) + 1 = M - i by omega] at ha
    by_cases h₂ : i < b
    · rw [midSeg i (by omega) (by omega), midSeg (i+1) (by omega) (by omega)]
      have ha := hadj (s + (i-M)) (by omega) (by omega)
      rwa [show s + (i-M) + 1 = s + (i+1-M) by omega] at ha
    · rw [rightSeg i (by omega), rightSeg (i+1) (by omega)]
      have ha := (step _ ht (i-b) (by omega)).symm
      rwa [show i - b + 1 = i + 1 - b by omega] at ha
  · intro i j hij hj he
    have hdepth := congrArg depth he
    by_cases hj₁ : j < M
    · have := ldep i (by omega)
      have := ldep j (by omega)
      omega
    by_cases hj₂ : j ≤ b
    · have := mdep j (by omega) hj₂
      by_cases hi₁ : i < M
      · have := ldep i (by omega)
        omega
      · rw [midSeg i (by omega) (by omega), midSeg j (by omega) hj₂] at he
        have := hinj _ _ (by omega) (by omega) (by omega) (by omega) he
        omega
    have hr := rdep j (by omega) (by omega)
    by_cases hi₁ : i < M
    · have hl := ldep i (by omega)
      have hidx : M-i = j-b := by omega
      rw [leftSeg i (by omega), rightSeg j (by omega), hidx] at he
      exact disj (j-b) (by omega) he
    by_cases hi₂ : i ≤ b
    · have := mdep i (by omega) hi₂
      omega
    · have := rdep i (by omega) (by omega)
      omega

/-- Clé de l'ordre en profondeur : en base `card V`, les chiffres sont `x`, son parent, son
grand-parent… ; le chiffre de poids fort est l'ancêtre le plus haut. -/
noncomputable def key (par : V → V) (e : ℕ) (x : V) : ℕ :=
  ∑ i ∈ Finset.range e, ((Fintype.equivFin V) (par^[i] x) : ℕ) * (Fintype.card V) ^ i

theorem key_add (par : V → V) (m e : ℕ) (x : V) :
    key par (m + e) x = key par m x + Fintype.card V ^ m * key par e (par^[m] x) := by
  unfold key
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [add_comm m j, Function.iterate_add_apply, pow_add]
  ring

theorem key_lt (par : V → V) (m : ℕ) (x : V) : key par m x < Fintype.card V ^ m := by
  induction m with
  | zero => simp [key]
  | succ m ih =>
    have h2 : ((Fintype.equivFin V) (par^[m] x) : ℕ) + 1 ≤ Fintype.card V := Fin.is_lt _
    have e : key par (m + 1) x = key par m x +
        ((Fintype.equivFin V) (par^[m] x) : ℕ) * Fintype.card V ^ m := by
      unfold key
      rw [Finset.sum_range_succ]
    have h3 := Nat.mul_le_mul_right (Fintype.card V ^ m) h2
    rw [e, pow_succ]
    nlinarith

theorem key_mod (par : V → V) (m e : ℕ) (x : V) :
    key par (m + e) x % Fintype.card V ^ m = key par m x := by
  rw [key_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (key_lt par m x)]

theorem key_div (par : V → V) (m e : ℕ) (x : V) (hV : 0 < Fintype.card V) :
    key par (m + e) x / Fintype.card V ^ m = key par e (par^[m] x) := by
  rw [key_add, Nat.add_mul_div_left _ _ (pow_pos hV m), Nat.div_eq_of_lt (key_lt par m x),
    zero_add]

theorem key_inj (par : V → V) (d : ℕ) (hd : 1 ≤ d) (x y : V)
    (h : key par d x = key par d y) : x = y := by
  have hm := key_mod par 1 (d - 1) x
  have hm' := key_mod par 1 (d - 1) y
  rw [show 1 + (d - 1) = d by omega] at hm hm'
  rw [h, hm'] at hm
  have h1 : ∀ z : V, key par 1 z = ((Fintype.equivFin V) z : ℕ) := by
    intro z
    simp [key]
  rw [h1, h1] at hm
  exact (Fintype.equivFin V).injective (Fin.ext hm.symm)

/-- Les descendants d'un même sommet forment un intervalle pour la clé. -/
theorem key_interval (par : V → V) (d m : ℕ) (hm : m < d) (x y w : V)
    (hxy : key par d x ≤ key par d y) (hyw : key par d y ≤ key par d w)
    (hxw : par^[m] x = par^[m] w) : par^[m] y = par^[m] x := by
  have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hd : d = m + (d - m) := by omega
  have e1 := key_div par m (d - m) x hV
  have e2 := key_div par m (d - m) y hV
  have e3 := key_div par m (d - m) w hV
  rw [← hd] at e1 e2 e3
  have h1 : key par d x / Fintype.card V ^ m ≤ key par d y / Fintype.card V ^ m :=
    Nat.div_le_div_right hxy
  have h2 : key par d y / Fintype.card V ^ m ≤ key par d w / Fintype.card V ^ m :=
    Nat.div_le_div_right hyw
  rw [e1, e2] at h1
  rw [e2, e3, ← hxw] at h2
  exact key_inj par (d - m) (by omega) _ _ (le_antisymm h2 h1)

/-- Chemin croissant pour la clé, à `m` sommets de `W`, qui finit en `x`. -/
def incPath (G : SimpleGraph V) (par : V → V) (d : ℕ) (W : Finset V) (x : V) (m : ℕ) : Prop :=
  ∃ g : ℕ → V, g (m - 1) = x ∧ ∀ r, r < m → g r ∈ W ∧
    (r + 1 < m → G.Adj (g r) (g (r + 1)) ∧ key par d (g r) < key par d (g (r + 1)))

theorem iterate_lift (par : V → V) (j j' : ℕ) (z z' : V) (hj : j ≤ j')
    (h : par^[j] z = par^[j] z') : par^[j'] z = par^[j'] z' := by
  have h' := congrArg (par^[j' - j]) h
  rwa [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.sub_add_cancel hj] at h'

/-- Sans cycle de longueur `2ℓ + 1`, un chemin croissant de la couche a au plus `2ℓ - 1` sommets. -/
theorem incPath_bound (G : SimpleGraph V) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hfree : ¬ cycleGraph (2 * ℓ + 1) ⊑ G)
    (depth : V → ℕ) (par : V → V) (d : ℕ) (hd1 : 1 ≤ d) (hdℓ : d ≤ ℓ)
    (hpar : ∀ y, 1 ≤ depth y → depth y ≤ d → G.Adj (par y) y ∧ depth (par y) + 1 = depth y)
    (hroot : ∀ x y, depth x = 0 → depth y = 0 → x = y)
    (W : Finset V) (hW : ∀ x ∈ W, depth x = d) (x : V) (m : ℕ)
    (hP : incPath G par d W x m) : m ≤ 2 * ℓ - 1 := by
  by_contra hm
  obtain ⟨g, -, hg⟩ := hP
  have hW' : ∀ r, r < 2 * ℓ → g r ∈ W := fun r hr => (hg r (by omega)).1
  have hadj' : ∀ r, r + 1 < 2 * ℓ → G.Adj (g r) (g (r + 1)) :=
    fun r hr => ((hg r (by omega)).2 (by omega)).1
  have hkey : ∀ r, r + 1 < 2 * ℓ → key par d (g r) < key par d (g (r + 1)) :=
    fun r hr => ((hg r (by omega)).2 (by omega)).2
  have strict : ∀ r n, r + n + 1 < 2 * ℓ → key par d (g r) < key par d (g (r + n + 1)) := by
    intro r n
    induction n with
    | zero => intro h; exact hkey r h
    | succ n ih =>
      intro h
      have h2 := hkey (r + n + 1) (by omega)
      rw [show r + n + 1 + 1 = r + (n + 1) + 1 by omega] at h2
      exact (ih (by omega)).trans h2
  have mono : ∀ r r', r ≤ r' → r' < 2 * ℓ → key par d (g r) ≤ key par d (g r') := by
    intro r r' h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · rw [h]
    · have h3 := strict r (r' - r - 1) (by omega)
      rw [show r + (r' - r - 1) + 1 = r' by omega] at h3
      exact h3.le
  have inj : ∀ r r', r < 2 * ℓ → r' < 2 * ℓ → g r = g r' → r = r' := by
    intro r r' h1 h2 he
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h3 := strict r (r' - r - 1) (by omega)
      rw [show r + (r' - r - 1) + 1 = r' by omega, he] at h3
      exact lt_irrefl _ h3
    · have h3 := strict r' (r - r' - 1) (by omega)
      rw [show r' + (r - r' - 1) + 1 = r by omega, he] at h3
      exact lt_irrefl _ h3
  have dep : ∀ z, depth z = d → ∀ i, i ≤ d → depth (par^[i] z) + i = d := by
    intro z hz i
    induction i with
    | zero => intro _; simpa using hz
    | succ i ih =>
      intro hi
      have h := ih (by omega)
      have hp := (hpar (par^[i] z) (by omega) (by omega)).2
      rw [Function.iterate_succ_apply']
      omega
  have top : ∀ r, r + 1 < 2 * ℓ → par^[d] (g r) = par^[d] (g (r + 1)) := by
    intro r hr
    apply hroot
    · have := dep _ (hW _ (hW' r (by omega))) d le_rfl
      omega
    · have := dep _ (hW _ (hW' (r + 1) hr)) d le_rfl
      omega
  have hex : ∀ r, ∃ j, 1 ≤ j ∧ (r + 1 < 2 * ℓ → par^[j] (g r) = par^[j] (g (r + 1))) :=
    fun r => ⟨d, hd1, top r⟩
  obtain ⟨s, r, t, hsr, hrt, ht, hlen, hmax⟩ := window ℓ hℓ (fun r => Nat.find (hex r))
    (fun r _ => ⟨(Nat.find_spec (hex r)).1, (Nat.find_min' (hex r) ⟨hd1, top r⟩).trans hdℓ⟩)
  set M := Nat.find (hex r) with hMdef
  have hM1 : 1 ≤ M := (Nat.find_spec (hex r)).1
  have hMd : M ≤ d := Nat.find_min' (hex r) ⟨hd1, top r⟩
  have step : ∀ r', s ≤ r' → r' < t → par^[M] (g r') = par^[M] (g (r' + 1)) := by
    intro r' h1 h2
    exact iterate_lift par _ _ _ _ (hmax r' h1 h2) ((Nat.find_spec (hex r')).2 (by omega))
  have chain : ∀ n, s + n ≤ t → par^[M] (g s) = par^[M] (g (s + n)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro h
      rw [ih (by omega)]
      have h2 := step (s + n) (by omega) (by omega)
      rwa [Nat.add_assoc] at h2
  have hmeet : par^[M] (g s) = par^[M] (g t) := by
    have h2 := chain (t - s) (by omega)
    rwa [show s + (t - s) = t by omega] at h2
  have hsplit : par^[M - 1] (g s) ≠ par^[M - 1] (g t) := by
    intro he
    have e1 := key_interval par d (M - 1) (by omega) (g s) (g r) (g t)
      (mono s r hsr (by omega)) (mono r t hrt.le (by omega)) he
    have e2 := key_interval par d (M - 1) (by omega) (g s) (g (r + 1)) (g t)
      (mono s (r + 1) (by omega) (by omega)) (mono (r + 1) t hrt (by omega)) he
    have e3 : par^[M - 1] (g r) = par^[M - 1] (g (r + 1)) := e1.trans e2.symm
    by_cases hM : M = 1
    · simp only [hM, Nat.sub_self, Function.iterate_zero, id_eq] at e3
      have := inj r (r + 1) (by omega) (by omega) e3
      omega
    · exact Nat.find_min (hex r) (show M - 1 < Nat.find (hex r) by omega) ⟨by omega, fun _ => e3⟩
  have hcyc := cycle_of_branches G depth par d hpar g s t (by omega)
    (fun r' _ h2 => hW _ (hW' r' (by omega)))
    (fun r' _ h2 => hadj' r' (by omega))
    (fun r1 r2 _ h2 _ h4 he => inj r1 r2 (by omega) (by omega) he)
    M hM1 hMd hmeet hsplit
  rw [show 2 * M + (t - s) = 2 * ℓ + 1 by omega] at hcyc
  exact hfree hcyc

/-- Borne d'EFRS : sans cycle de longueur `2ℓ + 1`, la couche de profondeur `d ≤ ℓ` d'un arbre
enraciné se colore avec `2ℓ - 1` couleurs. -/
theorem efrs (G : SimpleGraph V) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hfree : ¬ cycleGraph (2 * ℓ + 1) ⊑ G)
    (depth : V → ℕ) (par : V → V) (d : ℕ) (hd1 : 1 ≤ d) (hdℓ : d ≤ ℓ)
    (hpar : ∀ y, 1 ≤ depth y → depth y ≤ d → G.Adj (par y) y ∧ depth (par y) + 1 = depth y)
    (hroot : ∀ x y, depth x = 0 → depth y = 0 → x = y)
    (W : Finset V) (hW : ∀ x ∈ W, depth x = d) :
    ∃ g : V → Fin (2 * ℓ - 1), ∀ x ∈ W, ∀ y ∈ W, G.Adj x y → g x ≠ g y := by
  have bound := incPath_bound G ℓ hℓ hfree depth par d hd1 hdℓ hpar hroot W hW
  have P1 : ∀ x ∈ W, incPath G par d W x 1 :=
    fun x hx => ⟨fun _ => x, rfl, fun r _ => ⟨hx, fun h => by omega⟩⟩
  have colspec : ∀ x ∈ W,
      incPath G par d W x (Nat.findGreatest (incPath G par d W x) (2 * ℓ - 1)) :=
    fun x hx => Nat.findGreatest_spec (by omega) (P1 x hx)
  have colpos : ∀ x ∈ W, 1 ≤ Nat.findGreatest (incPath G par d W x) (2 * ℓ - 1) :=
    fun x hx => Nat.le_findGreatest (by omega) (P1 x hx)
  have extend : ∀ x ∈ W, ∀ y ∈ W, G.Adj x y → key par d x < key par d y →
      Nat.findGreatest (incPath G par d W x) (2 * ℓ - 1) + 1 ≤
        Nat.findGreatest (incPath G par d W y) (2 * ℓ - 1) := by
    intro x hx y hy hxy hk
    have hc1 := colpos x hx
    obtain ⟨g, hg1, hg2⟩ := colspec x hx
    set c := Nat.findGreatest (incPath G par d W x) (2 * ℓ - 1) with hc
    have hP : incPath G par d W y (c + 1) := by
      refine ⟨fun r => if r < c then g r else y, by simp, ?_⟩
      intro r hr
      by_cases hr' : r < c
      · refine ⟨by simpa [hr'] using (hg2 r hr').1, fun hr2 => ?_⟩
        by_cases hr3 : r + 1 < c
        · simpa [hr', hr3] using (hg2 r hr').2 hr3
        · have hrc : r = c - 1 := by omega
          simp only [hr', hr3, if_true, if_false]
          rw [hrc, hg1]
          exact ⟨hxy, hk⟩
      · refine ⟨by simpa [hr'] using hy, fun hr2 => by omega⟩
    exact Nat.le_findGreatest (bound y _ hP) hP
  refine ⟨fun x => ⟨Nat.findGreatest (incPath G par d W x) (2 * ℓ - 1) - 1, by
    have := Nat.findGreatest_le (P := incPath G par d W x) (2 * ℓ - 1)
    omega⟩, ?_⟩
  intro x hx y hy hxy he
  have he' : Nat.findGreatest (incPath G par d W x) (2 * ℓ - 1) - 1 =
      Nat.findGreatest (incPath G par d W y) (2 * ℓ - 1) - 1 := congrArg Fin.val he
  have hne : x ≠ y := G.ne_of_adj hxy
  have hk : key par d x ≠ key par d y := fun h => hne (key_inj par d hd1 x y h)
  rcases Nat.lt_or_gt_of_ne hk with h | h
  · have h1 := extend x hx y hy hxy h
    have h2 := colpos x hx
    omega
  · have h1 := extend y hy x hx hxy.symm h
    have h2 := colpos y hy
    omega

theorem ball_colouring_of (G : SimpleGraph V) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hefrs : ∀ (depth : V → ℕ) (par : V → V) (d : ℕ), 1 ≤ d → d ≤ ℓ →
      (∀ y, 1 ≤ depth y → depth y ≤ d → G.Adj (par y) y ∧ depth (par y) + 1 = depth y) →
      (∀ x y, depth x = 0 → depth y = 0 → x = y) →
      ∀ (W : Finset V), (∀ x ∈ W, depth x = d) →
      ∃ g : V → Fin (2 * ℓ - 1), ∀ x ∈ W, ∀ y ∈ W, G.Adj x y → g x ≠ g y)
    (U : Finset V) (v : V) (hv : v ∈ U) (d : ℕ) (hd : d ≤ ℓ) :
    ∃ f : V → Fin (4 * ℓ - 2), ∀ x ∈ ball G.Adj U v d, ∀ y ∈ ball G.Adj U v d,
      G.Adj x y → f x ≠ f y := by
  classical
  let B := ball G.Adj U v
  have suc (i : ℕ) : B (i+1) = B i ∪ U.filter (fun y => ∃ x ∈ B i, G.Adj x y) := rfl
  have subU (i : ℕ) : B i ⊆ U := by
    induction i with
    | zero => simpa [B, ball] using hv
    | succ i ih =>
      intro y hy
      rw [suc, Finset.mem_union] at hy
      exact hy.elim (fun h => ih h) (fun h => (Finset.mem_filter.mp h).1)
  have step (i : ℕ) {x y : V} (hx : x ∈ B i) (hy : y ∈ U) (hxy : G.Adj x y) : y ∈ B (i+1) := by
    rw [suc]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, x, hx, hxy⟩)
  let depth (x : V) := if h : ∃ i, x ∈ B i then Nat.find h else d + 1
  have leDepth {x : V} {i : ℕ} (hx : x ∈ B i) : depth x ≤ i := by
    have h : ∃ j, x ∈ B j := ⟨i, hx⟩
    simpa only [depth, dif_pos h] using (Nat.find_le (h := h) hx)
  have memDepth {x : V} (hx : depth x ≤ d) : x ∈ B (depth x) := by
    by_cases h : ∃ j, x ∈ B j
    · simpa only [depth, dif_pos h] using Nat.find_spec h
    · simp only [depth, dif_neg h] at hx
      omega
  have root {x : V} (hx : depth x = 0) : x = v := by
    have h := memDepth (x := x) (by omega)
    rw [hx] at h
    simpa [B, ball] using h
  let Pred (y x : V) : Prop :=
    1 ≤ depth y → depth y ≤ d → G.Adj x y ∧ depth x + 1 = depth y
  have predEx (y : V) : ∃ x, Pred y x := by
    by_cases hy : 1 ≤ depth y ∧ depth y ≤ d
    · obtain ⟨hy1, hyd⟩ := hy
      let k := depth y - 1
      have hk : k + 1 = depth y := by dsimp [k]; omega
      have hm := memDepth hyd
      have hyU := subU _ hm
      rw [← hk, suc, Finset.mem_union] at hm
      rcases hm with hm | hm
      · have hbad := leDepth hm
        omega
      · obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hm).2
        have hle := leDepth hx
        have hx' := memDepth (x := x) (by omega)
        have hge := leDepth (step _ hx' hyU hxy)
        exact ⟨x, fun _ _ => ⟨hxy, by omega⟩⟩
    · exact ⟨y, fun h₁ h₂ => (hy ⟨h₁, h₂⟩).elim⟩
  choose par hpar using predEx
  let W (e : ℕ) := Finset.univ.filter (fun y : V => depth y = e)
  have memW {x : V} {e : ℕ} : x ∈ W e ↔ depth x = e := by simp [W]
  let Proper (e : ℕ) (g : V → Fin (2 * ℓ - 1)) : Prop :=
    1 ≤ e → e ≤ d → ∀ x ∈ W e, ∀ y ∈ W e, G.Adj x y → g x ≠ g y
  have colours (e : ℕ) : ∃ g, Proper e g := by
    by_cases he : 1 ≤ e ∧ e ≤ d
    · obtain ⟨g, hg⟩ := hefrs depth par e he.1 (he.2.trans hd)
          (fun y h₁ h₂ => hpar y h₁ (h₂.trans he.2))
          (fun _ _ hx hy => (root hx).trans (root hy).symm) (W e) (fun _ h => memW.mp h)
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨fun _ => ⟨0, by omega⟩, fun h₁ h₂ => (he ⟨h₁, h₂⟩).elim⟩
  choose g hg using colours
  let a (x : V) := (g (depth x) x).val
  have alt (x : V) : a x < 2 * ℓ - 1 := (g (depth x) x).isLt
  let f (x : V) : Fin (4 * ℓ - 2) :=
    ⟨if depth x % 2 = 0 then a x else (2 * ℓ - 1) + a x, by have := alt x; split <;> omega⟩
  refine ⟨f, ?_⟩
  intro x hx y hy hxy heq
  have hxd := leDepth hx
  have hyd := leDepth hy
  have h₁ := leDepth (step _ (memDepth hxd) (subU d hy) hxy)
  have h₂ := leDepth (step _ (memDepth hyd) (subU d hx) hxy.symm)
  have hval := congrArg Fin.val heq
  change (if depth x % 2 = 0 then a x else (2 * ℓ - 1) + a x) =
    (if depth y % 2 = 0 then a y else (2 * ℓ - 1) + a y) at hval
  have hax := alt x
  have hay := alt y
  have h : depth x = depth y ∧ a x = a y := by
    split at hval <;> split at hval <;> constructor <;> omega
  by_cases hz : depth x = 0
  · exact hxy.ne ((root hz).trans (root (h.1.symm.trans hz)).symm)
  · apply hg (depth x) (by omega) hxd x (memW.mpr rfl) y (memW.mpr h.1.symm) hxy
    apply Fin.ext
    have ha := h.2
    change (g (depth x) x).val = (g (depth y) y).val at ha
    rwa [← h.1] at ha

/-- Les boules de rayon `d ≤ ℓ` se colorent avec `4ℓ - 2` couleurs (couches paires et impaires). -/
theorem ball_colouring (G : SimpleGraph V) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hfree : ¬ cycleGraph (2 * ℓ + 1) ⊑ G) (U : Finset V) (v : V) (hv : v ∈ U)
    (d : ℕ) (hd : d ≤ ℓ) :
    ∃ f : V → Fin (4 * ℓ - 2), ∀ x ∈ ball G.Adj U v d, ∀ y ∈ ball G.Adj U v d,
      G.Adj x y → f x ≠ f y := by
  exact ball_colouring_of G ℓ hℓ (fun depth par e he1 heℓ hpar hroot W hW =>
    efrs G ℓ hℓ hfree depth par e he1 heℓ hpar hroot W hW) U v hv d hd

theorem no_mono_bound (n k N : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (C : TopEdgeLabeling (Fin N) (Fin k))
    (hfree : ∀ c, ¬ cycleGraph (2 * n + 1) ⊑ C.labelGraph c) :
    (N : ℝ) ≤ (4 * n - 2 : ℝ) ^ k * (k : ℝ) ^ ((k : ℝ) / n) := by
  have h := weight_lemma (V := Fin N) (fun c => (C.labelGraph c).Adj)
    (fun c x y h => h.symm) (fun c x => (C.labelGraph c).irrefl)
    (fun x y hxy => ⟨C.get x y hxy, (TopEdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, rfl⟩⟩)
    (4 * n - 2) n (by omega) hn hk
    (fun U v hv c d _ hd => ball_colouring (C.labelGraph c) n hn (hfree c) U v hv d hd)
  rw [Fintype.card_fin] at h
  have e : ((4 * n - 2 : ℕ) : ℝ) = (4 * n - 2 : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e] at h
  exact h

end OMA554A

private theorem bound_acjmr : type_of% @Erdos554.erdos_554.variants.acjmr := by
  intro n hn k hk
  have h1 : (0 : ℝ) ≤ 4 * n - 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hB0 : (0 : ℝ) ≤ (4 * n - 2 : ℝ) ^ k * (k : ℝ) ^ ((k : ℝ) / n) :=
    mul_nonneg (pow_nonneg h1 k) (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hmem : ⌊(4 * n - 2 : ℝ) ^ k * (k : ℝ) ^ ((k : ℝ) / n)⌋₊ + 1 ∈ {N : ℕ | ∀ C :
      TopEdgeLabeling (Fin N) (Fin k), ∃ i, (cycleGraph (2 * n + 1)).IsContained
        (C.labelGraph i)} := by
    intro C
    by_contra hcon
    push Not at hcon
    have h := OMA554A.no_mono_bound n k _ hn hk C (fun c ⟨f⟩ => (hcon c).false f)
    have := Nat.lt_floor_add_one ((4 * n - 2 : ℝ) ^ k * (k : ℝ) ^ ((k : ℝ) / n))
    push_cast at h
    linarith
  have hle := Nat.sInf_le hmem
  have h2 : (SimpleGraph.multicolourGraphRamsey k (cycleGraph (2 * n + 1)) : ℝ) ≤
      ⌊(4 * n - 2 : ℝ) ^ k * (k : ℝ) ^ ((k : ℝ) / n)⌋₊ + 1 := by
    exact_mod_cast hle
  have := Nat.floor_le hB0
  linarith

open Filter SimpleGraph
theorem OMA.solution : OMA.R_Erdos554_erdos_554_R1.H2 := by
  intro n hn
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have h := bound_acjmr n (by omega) k hk
  apply h.trans
  have hb : 4 * n - 2 < 4 * n := by omega
  have hpow : (4 * n - 2) ^ k + 1 ≤ (4 * n) ^ k :=
    Nat.succ_le_of_lt (Nat.pow_lt_pow_left hb (by omega))
  have hcast : (4 * (n : ℝ) - 2) ^ k + 1 ≤ (4 * (n : ℝ)) ^ k := by
    have he : ((4 * n - 2 : ℕ) : ℝ) = 4 * (n : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← he]
    exact_mod_cast hpow
  have hx : (1 : ℝ) ≤ (k : ℝ) ^ ((k : ℝ) / n) := Real.one_le_rpow (by exact_mod_cast hk) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hcast (zero_le_one.trans hx)]
