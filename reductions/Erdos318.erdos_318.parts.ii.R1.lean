import FormalConjectures.ErdosProblems.«318»

-- Reduction Erdos318.erdos_318.parts.ii.R1 of Erdős Problem 318 — ii
-- Credit: @iLc0
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 318 (ii) : la preuve de Larsen, réduite à son théorème « circle »

Larsen (2026, th. 3) : toute partition non triviale des carrés `> 1` en `X ⊔ Y` admet deux parties
finies non vides `X' ⊆ X`, `Y' ⊆ Y` de même somme d'inverses ; c'est `P₁` pour ces carrés.

Notations (`N` grand) : `B` = carrés `N`-friables `< N²·4^N` ; `Q` = carrés des premiers de
`]N, N·2^N[` ; `Z = {b·∏Q' : b ∈ B, Q' ⊆ Q}` ; `E` = éléments de `B` sous `N⁴` ; `D = Z \ E`.

* `H1` : le théorème « circle » de Larsen (th. 2, `β = 1/2`, `ε = 1`) appliqué à `D` : pour une
  cible `q = w(T) − w(S)` (`T ⊆ Z`, `S ⊆ E`) avec `1,01·q ≤ w(D) ≤ 100·q`, deux parties distinctes
  de `D` ont une somme d'inverses `≡ q (mod 1)`. Paramètres du th. 2 : `ℓ/k = q`, `y_i = N²·2^(i-1)`
  (`1 ≤ i ≤ 2N`), `Q_i` = carrés des premiers de `[√y_i, √(2y_i))`, `B` et `E` comme ci-dessus
  (`E` contient tout `B ∩ [1, y_1²)`), `k ∣ ppcm(D)` car `b·q ∈ D` pour `b ∈ E`, `q ∈ Q` ; Larsen
  vérifie l'hypothèse H dans la preuve de son th. 3. Les deux bornes du rapport forcent `0 < q < 1`.
* `H2` : les carrés `≥ 4` hors de `Z` pèsent au plus `1/(10N²)` (un tel `n²` a un facteur `p⁴`,
  `p > N` premier, ou dépasse `N²·4^N`).
* `main` : un glouton sur les petits carrés `d²` de `E` (`2 ≤ d < N²`) ramène le rapport
  `w(D)/q` dans `[1,01 ; 100]`, puis `H1` fournit une partie `Z' ≠ Y ∩ Z` de même somme que
  `Y ∩ Z` ; `Z' \ Y` et `(Y ∩ Z) \ Z'` conviennent.
-/

namespace OMA.R_Erdos318_erdos_318_parts_ii_R1

open Finset

def H1 : Prop := ∃ N₀ : ℕ, ∀ N ≥ N₀,
  let B : Finset ℕ := ((range (N * 2 ^ N)).filter
    (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
  let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
  let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
  let E : Finset ℕ := B.filter (· < N ^ 4)
  ∀ T ⊆ Z, ∀ S ⊆ E,
    (101 / 100 : ℝ) * (∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s) ≤ ∑ d ∈ Z \ E, (1 : ℝ) / d →
    ∑ d ∈ Z \ E, (1 : ℝ) / d ≤ 100 * (∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s) →
    ∃ D₁ D₂ : Finset ℕ, D₁ ⊆ Z \ E ∧ D₂ ⊆ Z \ E ∧ D₁ ≠ D₂ ∧
      (∃ k : ℤ, ∑ d ∈ D₁, (1 : ℝ) / d = ∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s + k) ∧
      (∃ k : ℤ, ∑ d ∈ D₂, (1 : ℝ) / d = ∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s + k)

def H2 : Prop := ∃ N₁ : ℕ, ∀ N ≥ N₁,
  let B : Finset ℕ := ((range (N * 2 ^ N)).filter
    (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2)
  let Q : Finset ℕ := ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2)
  let Z : Finset ℕ := (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q)
  ∀ M : ℕ, ∑ n ∈ (Ico 2 M).filter (fun n => n ^ 2 ∉ Z), (1 : ℝ) / n ^ 2 ≤ 1 / (10 * N ^ 2)

theorem p1_of_core
    (core : ∀ X : Set ℕ, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → a ^ 2 ∈ X → b ^ 2 ∉ X →
      ∃ X' Y' : Finset ℕ, X'.Nonempty ∧
        (∀ n ∈ X', n ∈ X ∧ IsSquare n ∧ 1 < n) ∧ (∀ n ∈ Y', n ∉ X ∧ IsSquare n ∧ 1 < n) ∧
        ∑ n ∈ X', (1 : ℝ) / n = ∑ n ∈ Y', (1 : ℝ) / n) :
    Erdos318.P₁ ({n | IsSquare n} \ {1}) := by
  classical
  intro f hf1 hfm1 hrange
  have hval : ∀ n, f n = 1 ∨ f n = -1 := fun n => by
    have h := hrange ⟨n, rfl⟩
    simpa using h
  have hmem : ∀ n : ℕ, n ∈ ({n | IsSquare n} \ {1} : Set ℕ) \ {0} ↔ IsSquare n ∧ 1 < n := by
    intro n
    simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, by omega⟩
  have hex : ∀ v : ℝ,
      (f ∘ (Subtype.val : (({n | IsSquare n} \ {1} : Set ℕ) \ {0} : Set ℕ) → ℕ) ≠ fun _ => v) →
      ∃ y : ℕ, IsSquare y ∧ 1 < y ∧ f y ≠ v := by
    intro v hne
    by_contra hcon
    push_neg at hcon
    apply hne
    funext ⟨n, hn⟩
    obtain ⟨h1, h2⟩ := (hmem n).1 hn
    exact hcon n h1 h2
  obtain ⟨y, hyS, hy1, hyf⟩ := hex 1 hf1
  obtain ⟨x, hxS, hx1, hxf⟩ := hex (-1) hfm1
  have hyf' : f y = -1 := (hval y).resolve_left hyf
  have hxf' : f x = 1 := (hval x).resolve_right hxf
  obtain ⟨a, rfl⟩ := hxS
  obtain ⟨b, rfl⟩ := hyS
  have ha : 2 ≤ a := by
    by_contra h
    push_neg at h
    interval_cases a <;> simp at hx1
  have hb : 2 ≤ b := by
    by_contra h
    push_neg at h
    interval_cases b <;> simp at hy1
  obtain ⟨X', Y', hne, hX', hY', hsum⟩ := core {n | f n = 1} a b ha hb
    (by show f (a ^ 2) = 1; rw [sq]; exact hxf')
    (by show ¬ f (b ^ 2) = 1; rw [sq, hyf']; norm_num)
  refine ⟨X' ∪ Y', hne.mono subset_union_left, ?_, ?_⟩
  · intro n hn
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hn) with hn | hn
    · exact (hmem n).2 ⟨(hX' n hn).2.1, (hX' n hn).2.2⟩
    · exact (hmem n).2 ⟨(hY' n hn).2.1, (hY' n hn).2.2⟩
  · have hdisj : Disjoint X' Y' := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      exact (hY' n hn2).1 (hX' n hn1).1
    rw [Finset.sum_union hdisj]
    have h1 : ∑ n ∈ X', f n / n = ∑ n ∈ X', (1 : ℝ) / n := by
      apply Finset.sum_congr rfl
      intro n hn
      have : f n = 1 := (hX' n hn).1
      rw [this]
    have h2 : ∑ n ∈ Y', f n / n = -∑ n ∈ Y', (1 : ℝ) / n := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      have : f n = -1 := (hval n).resolve_left (hY' n hn).1
      rw [this, neg_div]
    rw [h1, h2, hsum]
    ring

theorem split_of_two_subsets (X : Set ℕ) (Z Z' Y : Finset ℕ)
    (hZ : ∀ n ∈ Z, IsSquare n ∧ 0 < n)
    (hY : ∀ n, n ∈ Y ↔ n ∈ Z ∧ 1 < n ∧ n ∉ X)
    (hZ'Z : Z' ⊆ Z) (h1 : 1 ∉ Z') (hne : Z' ≠ Y)
    (hsum : ∑ n ∈ Z', (1 : ℝ) / n = ∑ n ∈ Y, (1 : ℝ) / n) :
    ∃ X' Y' : Finset ℕ, X'.Nonempty ∧
      (∀ n ∈ X', n ∈ X ∧ IsSquare n ∧ 1 < n) ∧ (∀ n ∈ Y', n ∉ X ∧ IsSquare n ∧ 1 < n) ∧
      ∑ n ∈ X', (1 : ℝ) / n = ∑ n ∈ Y', (1 : ℝ) / n := by
  classical
  refine ⟨Z' \ Y, Y \ Z', ?_, ?_, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub : Z' ⊆ Y := Finset.sdiff_eq_empty_iff_subset.1 hempty
    have hss : Z' ⊂ Y := Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩
    obtain ⟨y, hyY, hyZ'⟩ := Finset.exists_of_ssubset hss
    have hlt : ∑ n ∈ Z', (1 : ℝ) / n < ∑ n ∈ Y, (1 : ℝ) / n := by
      apply Finset.sum_lt_sum_of_subset hsub hyY hyZ'
      · have h0 := (hZ y ((hY y).1 hyY).1).2
        positivity
      · intro j _ _
        positivity
    linarith
  · intro n hn
    rw [Finset.mem_sdiff] at hn
    obtain ⟨hnZ', hnY⟩ := hn
    have hnZ := hZ'Z hnZ'
    have hn1 : 1 < n := by
      have h0 := (hZ n hnZ).2
      rcases Nat.lt_or_ge 1 n with h | h
      · exact h
      · exfalso
        have : n = 1 := by omega
        exact h1 (this ▸ hnZ')
    refine ⟨?_, (hZ n hnZ).1, hn1⟩
    by_contra hX
    exact hnY ((hY n).2 ⟨hnZ, hn1, hX⟩)
  · intro n hn
    rw [Finset.mem_sdiff] at hn
    obtain ⟨h1', h2', h3'⟩ := (hY n).1 hn.1
    exact ⟨h3', (hZ n h1').1, h2'⟩
  · have e1 : ∑ n ∈ Z' \ Y, (1 : ℝ) / n + ∑ n ∈ Z' ∩ Y, (1 : ℝ) / n = ∑ n ∈ Z', (1 : ℝ) / n := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter Z' Y), Finset.sdiff_union_inter]
    have e2 : ∑ n ∈ Y \ Z', (1 : ℝ) / n + ∑ n ∈ Y ∩ Z', (1 : ℝ) / n = ∑ n ∈ Y, (1 : ℝ) / n := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter Y Z'), Finset.sdiff_union_inter]
    rw [Finset.inter_comm] at e2
    linarith

/-- Glouton : si chaque poids est au plus `κ = 1/(1+c) − c` fois ce qui reste après lui (plus
`R`), on peut retirer à `τ` une partie des poids pour finir dans `[c·R, R/(1+c)]`. -/
theorem greedy (t : ℕ → ℝ) (R c : ℝ) (hc : 0 < c) (hR : 0 ≤ R) :
    ∀ F : Finset ℕ, (∀ d ∈ F, 0 ≤ t d) →
      (∀ d ∈ F, t d ≤ (1 / (1 + c) - c) * (∑ e ∈ F.filter (fun e => d < e), t e + R)) →
      ∀ τ : ℝ, c * R ≤ τ → τ ≤ ∑ d ∈ F, t d + R / (1 + c) →
        ∃ S ⊆ F, c * R ≤ τ - ∑ d ∈ S, t d ∧ τ - ∑ d ∈ S, t d ≤ R / (1 + c) := by
  clear hR
  intro F
  induction F using Finset.induction_on_min with
  | empty =>
    intro _ _ τ hlo hhi
    refine ⟨∅, Subset.rfl, ?_, ?_⟩
    · simpa using hlo
    · simpa using hhi
  | insert a s hmin ih =>
    intro hpos hbound τ hlo hhi
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmin a h)
    have hs : ∀ d ∈ s, 0 ≤ t d := fun d hd => hpos d (mem_insert_of_mem hd)
    have hs' : ∀ d ∈ s, t d ≤ (1 / (1 + c) - c) *
        ((∑ e ∈ s.filter (fun e => d < e), t e) + R) := by
      intro d hd
      simpa [filter_insert, (hmin d hd).asymm] using hbound d (mem_insert_of_mem hd)
    rw [sum_insert ha] at hhi
    by_cases htake : c * R ≤ τ - t a
    · obtain ⟨S, hS, hl, hu⟩ := ih hs hs' (τ - t a) htake (by linarith)
      refine ⟨insert a S, insert_subset_insert _ hS, ?_⟩
      rw [sum_insert (fun h => ha (hS h))]
      constructor <;> linarith
    · have hf : s.filter (fun e => a < e) = s := filter_eq_self.mpr hmin
      have hb : t a ≤ (1 / (1 + c) - c) * ((∑ e ∈ s, t e) + R) := by
        simpa [filter_insert, hf] using hbound a (mem_insert_self a s)
      have hdiv : 1 / (1 + c) ≤ 1 := (div_le_iff₀ (by linarith)).2 (by linarith)
      have hsum : 0 ≤ ∑ e ∈ s, t e := sum_nonneg hs
      have hmul := mul_le_mul_of_nonneg_right (show 1 / (1 + c) - c ≤ 1 by linarith) hsum
      have heq : 1 / (1 + c) * R = R / (1 + c) := by ring
      have hupper : τ ≤ (∑ e ∈ s, t e) + R / (1 + c) := by
        linarith only [lt_of_not_ge htake, hb, hmul, heq]
      obtain ⟨S, hS, hl, hu⟩ := ih hs hs' τ hlo hupper
      exact ⟨S, hS.trans (subset_insert a s), hl, hu⟩

theorem sum_squares_le (N : ℕ) (D : Finset ℕ) (hD : ∀ d ∈ D, IsSquare d ∧ N ^ 2 < d) :
    ∑ d ∈ D, (1 : ℝ) / d ≤ 2 / (N + 1) := by
  classical
  set M := D.sup id + 1 with hM
  set R := (Ioo N M).filter (fun n => n ^ 2 ∈ D) with hR
  have hDR : D = R.image (· ^ 2) := by
    ext d
    constructor
    · intro hd
      obtain ⟨⟨r, hr⟩, hlt⟩ := hD d hd
      subst hr
      have hdle : r * r ≤ D.sup id := Finset.le_sup (f := id) hd
      have hNr : N < r := by
        by_contra h
        push_neg at h
        have : r * r ≤ N * N := Nat.mul_le_mul h h
        nlinarith
      refine Finset.mem_image.2 ⟨r, Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨hNr, ?_⟩, by rw [sq]; exact hd⟩, by rw [sq]⟩
      have : r ≤ r * r := Nat.le_mul_of_pos_left r (by omega)
      omega
    · intro hd
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hd
      exact (Finset.mem_filter.1 hr).2
  rw [hDR, Finset.sum_image (fun x _ y _ h => Nat.pow_left_injective (by norm_num) h)]
  have h1 : ∑ n ∈ R, (1 : ℝ) / ((n ^ 2 : ℕ) : ℝ) = ∑ n ∈ R, ((n : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    rw [one_div]
  have h2 : ∑ n ∈ R, ((n : ℝ) ^ 2)⁻¹ ≤ ∑ n ∈ Ioo N M, ((n : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => by positivity)
  have h3 := sum_Ioo_inv_sq_le (α := ℝ) N M
  rw [h1]
  linarith

theorem tail_lower (d M : ℕ) (hdM : d + 1 ≤ M) :
    1 / ((d : ℝ) + 1) - 1 / M ≤ ∑ n ∈ Ico (d + 1) M, (1 : ℝ) / (n : ℝ) ^ 2 := by
  induction M, hdM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have key : (1 : ℝ) / M - 1 / ((M + 1 : ℕ) : ℝ) ≤ 1 / (M : ℝ) ^ 2 := by
      push_cast
      rw [div_sub_div _ _ (ne_of_gt hM0) (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- Si les carrés `≥ 4` hors de `Z` pèsent au plus `δ`, la masse de `Z` au-dessus de `d²` est au
moins `1/(d+1) − δ`. -/
theorem mass_above (Z : Finset ℕ) (δ : ℝ)
    (hδ : ∀ M : ℕ, ∑ n ∈ (Ico 2 M).filter (fun n => n ^ 2 ∉ Z), (1 : ℝ) / n ^ 2 ≤ δ)
    (d : ℕ) (hd : 1 ≤ d) :
    1 / ((d : ℝ) + 1) - δ ≤ ∑ z ∈ Z.filter (fun z => d ^ 2 < z), (1 : ℝ) / z := by
  classical
  have key : ∀ M : ℕ, d + 1 ≤ M →
      1 / ((d : ℝ) + 1) - 1 / M - δ ≤ ∑ z ∈ Z.filter (fun z => d ^ 2 < z), (1 : ℝ) / z := by
    intro M hM
    have ht := tail_lower d M hM
    have hsplit := Finset.sum_filter_add_sum_filter_not (Ico (d + 1) M) (fun n => n ^ 2 ∈ Z)
      (fun n => (1 : ℝ) / (n : ℝ) ^ 2)
    have hA : ∑ n ∈ (Ico (d + 1) M).filter (fun n => n ^ 2 ∈ Z), (1 : ℝ) / (n : ℝ) ^ 2 ≤
        ∑ z ∈ Z.filter (fun z => d ^ 2 < z), (1 : ℝ) / z := by
      have himg : ((Ico (d + 1) M).filter (fun n => n ^ 2 ∈ Z)).image (fun n : ℕ => (n ^ 2 : ℕ)) ⊆
          Z.filter (fun z => d ^ 2 < z) := by
        intro z hz
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hz
        obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
        have := (Finset.mem_Ico.1 hn1).1
        refine Finset.mem_filter.2 ⟨hn2, ?_⟩
        exact Nat.pow_lt_pow_left (by omega) (by norm_num)
      calc ∑ n ∈ (Ico (d + 1) M).filter (fun n => n ^ 2 ∈ Z), (1 : ℝ) / (n : ℝ) ^ 2
          = ∑ z ∈ ((Ico (d + 1) M).filter (fun n => n ^ 2 ∈ Z)).image (fun n : ℕ => (n ^ 2 : ℕ)), (1 : ℝ) / z := by
            rw [Finset.sum_image (fun x _ y _ h => Nat.pow_left_injective (by norm_num) h)]
            simp only [Nat.cast_pow]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => by positivity)
    have hB : ∑ n ∈ (Ico (d + 1) M).filter (fun n => ¬ n ^ 2 ∈ Z), (1 : ℝ) / (n : ℝ) ^ 2 ≤ δ := by
      refine le_trans ?_ (hδ M)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn1
        exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, h2⟩, hn2⟩
      · intro i _ _
        positivity
    linarith
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  have hM' := key (M + d + 1) (by omega)
  have hlt : (1 : ℝ) / ((M + d + 1 : ℕ) : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hM
    push_cast
    nlinarith
  linarith

/-- L'inégalité numérique du glouton, `κ = 1/(1 + 1/100) − 1/100`. -/
theorem num_ineq (d N : ℕ) (hd : 2 ≤ d) (hdN : d + 1 ≤ N ^ 2) :
    (1 : ℝ) / (d : ℝ) ^ 2 ≤ (1 / (1 + 1 / 100) - 1 / 100) * (1 / ((d : ℝ) + 1) - 1 / (10 * (N : ℝ) ^ 2)) := by
  have hx : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hy : (d : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by exact_mod_cast hdN
  have hxpos : 0 < (d : ℝ) := by linarith
  have hmain : 1 / (d : ℝ) ^ 2 ≤ 3 / 4 * (1 / ((d : ℝ) + 1)) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ 3 * (d : ℝ) + 2 by positivity)]
  have htail : 1 / (10 * (N : ℝ) ^ 2) ≤ 1 / 10 * (1 / ((d : ℝ) + 1)) := by
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [hy])
  have hpos : 0 ≤ 1 / ((d : ℝ) + 1) := by positivity
  linarith only [hmain, htail, hpos]

/-- Structure de `Z` et de `E`. -/
theorem Zstruct (N : ℕ) (hN : 2 ≤ N) (B Q Z E : Finset ℕ)
    (hB : B = ((range (N * 2 ^ N)).filter
      (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ≤ N)).image (· ^ 2))
    (hQ : Q = ((range (N * 2 ^ N)).filter (fun p => p.Prime ∧ N < p)).image (· ^ 2))
    (hZ : Z = (B ×ˢ Q.powerset).image (fun x => x.1 * ∏ q ∈ x.2, q))
    (hE : E = B.filter (· < N ^ 4)) :
    (∀ z ∈ Z, IsSquare z ∧ 0 < z) ∧ E ⊆ Z ∧ 1 ∈ E ∧
      (∀ e ∈ E, e = 1 ∨ ∃ d : ℕ, 2 ≤ d ∧ d + 1 ≤ N ^ 2 ∧ e = d ^ 2) ∧
      (∀ d ∈ Z \ E, N ^ 2 < d) ∧ (Z \ E).Nonempty ∧
      (∀ a : ℕ, 2 ≤ a → a ≤ N → a ^ 2 ∈ Z) := by
  classical
  have hpos : 0 < N := by omega
  have hbound : N ^ 2 < N * 2 ^ N := by
    simpa only [sq] using Nat.mul_lt_mul_of_pos_left
      (show N < 2 ^ N from Nat.lt_two_pow_self) hpos
  have hNsq : N < N ^ 2 := by nlinarith only [hN]
  have hNfour : N ^ 2 < N ^ 4 := by
    calc
      N ^ 2 < (N ^ 2) ^ 2 := Nat.pow_lt_pow_left hNsq (by decide)
      _ = N ^ 4 := by ring
  have hBin {b : ℕ} : b ∈ B ↔ ∃ n : ℕ, n < N * 2 ^ N ∧ 0 < n ∧
      (∀ p ∈ n.primeFactors, p ≤ N) ∧ n ^ 2 = b := by
    rw [hB]
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨n, ⟨hr, hn, hp⟩, heq⟩
      exact ⟨n, hr, hn, hp, heq⟩
    · rintro ⟨n, hr, hn, hp, heq⟩
      exact ⟨n, ⟨hr, hn, hp⟩, heq⟩
  have hQinfo {q : ℕ} (hq : q ∈ Q) : IsSquare q ∧ N ^ 2 < q := by
    rw [hQ, mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨⟨p, sq p⟩, Nat.pow_lt_pow_left (mem_filter.mp hp).2.2 (by decide)⟩
  have hZin {z : ℕ} : z ∈ Z ↔ ∃ b ∈ B, ∃ s ⊆ Q, b * ∏ q ∈ s, q = z := by
    rw [hZ, mem_image]
    constructor
    · rintro ⟨⟨b, s⟩, hbs, rfl⟩
      exact ⟨b, (mem_product.mp hbs).1, s, mem_powerset.mp (mem_product.mp hbs).2, rfl⟩
    · rintro ⟨b, hb, s, hs, rfl⟩
      exact ⟨(b, s), mem_product.mpr ⟨hb, mem_powerset.mpr hs⟩, rfl⟩
  have hBZ : B ⊆ Z := by
    intro b hb
    exact hZin.mpr ⟨b, hb, ∅, empty_subset _, by simp⟩
  have hEin {e : ℕ} : e ∈ E ↔ e ∈ B ∧ e < N ^ 4 := by
    rw [hE, mem_filter]
  have hsmall {a : ℕ} (ha : 0 < a) (haN : a ≤ N) : a ^ 2 ∈ B :=
    hBin.mpr ⟨a, haN.trans_lt (hNsq.trans hbound), ha,
      fun _ hp => (Nat.le_of_mem_primeFactors hp).trans haN, rfl⟩
  have hprod {s : Finset ℕ} (hs : s ⊆ Q) : 0 < ∏ q ∈ s, q :=
    Finset.prod_pos fun q hq => (Nat.zero_le _).trans_lt (hQinfo (hs hq)).2
  refine ⟨?_, fun e he => hBZ (hEin.mp he).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, hb, s, hs, rfl⟩ := hZin.mp hz
    obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
    exact ⟨(show IsSquare (n ^ 2) from ⟨n, sq n⟩).mul
      (Finset.isSquare_prod (fun q => q) fun q hq => (hQinfo (hs hq)).1),
      Nat.mul_pos (pow_pos hn _) (hprod hs)⟩
  · apply hEin.mpr
    exact ⟨by simpa using hsmall (a := 1) (by decide) (by omega), by omega⟩
  · intro e he
    obtain ⟨hb, hlt⟩ := hEin.mp he
    obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
    by_cases h : n = 1
    · left
      simp [h]
    · right
      refine ⟨n, by omega, ?_, rfl⟩
      by_contra! hle
      have hge : N ^ 2 ≤ n := by omega
      have hsq : (N ^ 2) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hge 2
      nlinarith only [hsq, hlt]
  · intro d hd
    obtain ⟨hz, hne⟩ := mem_sdiff.mp hd
    obtain ⟨b, hb, s, hs, rfl⟩ := hZin.mp hz
    rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
    · simp only [prod_empty, mul_one] at hne ⊢
      exact hNfour.trans_le (le_of_not_gt fun h => hne (hEin.mpr ⟨hb, h⟩))
    · obtain ⟨n, _, hn, _, rfl⟩ := hBin.mp hb
      have hdvd := Finset.dvd_prod_of_mem (fun t : ℕ => t) hq
      have hle := Nat.le_of_dvd (hprod hs) hdvd
      calc
        N ^ 2 < q := (hQinfo (hs hq)).2
        _ ≤ ∏ t ∈ s, t := hle
        _ ≤ n ^ 2 * ∏ t ∈ s, t := Nat.le_mul_of_pos_left _ (pow_pos hn _)
  · have hfour : N ^ 4 ∈ B := by
      refine hBin.mpr ⟨N ^ 2, hbound, pow_pos hpos _, ?_, by ring⟩
      intro p hp
      rw [Nat.primeFactors_pow N (by decide : 2 ≠ 0)] at hp
      exact Nat.le_of_mem_primeFactors hp
    exact ⟨N ^ 4, mem_sdiff.mpr ⟨hBZ hfour, fun he => (lt_irrefl _) (hEin.mp he).2⟩⟩
  · intro a ha haN
    exact hBZ (hsmall (by omega) haN)

/-- L'assemblage du th. 3 à `N` fixé, à partir des propriétés de `Z`, `E`, de `H1` et de `H2`. -/
theorem assemble (N : ℕ) (hN : 2 ≤ N) (Z E : Finset ℕ)
    (hZsq : ∀ z ∈ Z, IsSquare z ∧ 0 < z) (hEZ : E ⊆ Z) (h1E : 1 ∈ E)
    (hEsq : ∀ e ∈ E, e = 1 ∨ ∃ d : ℕ, 2 ≤ d ∧ d + 1 ≤ N ^ 2 ∧ e = d ^ 2)
    (hD : ∀ d ∈ Z \ E, N ^ 2 < d) (hDne : (Z \ E).Nonempty)
    (hcirc : ∀ T ⊆ Z, ∀ S ⊆ E,
      (101 / 100 : ℝ) * (∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s) ≤ ∑ d ∈ Z \ E, (1 : ℝ) / d →
      ∑ d ∈ Z \ E, (1 : ℝ) / d ≤ 100 * (∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s) →
      ∃ D₁ D₂ : Finset ℕ, D₁ ⊆ Z \ E ∧ D₂ ⊆ Z \ E ∧ D₁ ≠ D₂ ∧
        (∃ k : ℤ, ∑ d ∈ D₁, (1 : ℝ) / d = ∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s + k) ∧
        (∃ k : ℤ, ∑ d ∈ D₂, (1 : ℝ) / d = ∑ t ∈ T, (1 : ℝ) / t - ∑ s ∈ S, (1 : ℝ) / s + k))
    (hmass : ∀ M : ℕ, ∑ n ∈ (Ico 2 M).filter (fun n => n ^ 2 ∉ Z), (1 : ℝ) / n ^ 2 ≤ 1 / (10 * N ^ 2))
    (X : Set ℕ) (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (haZ : a ^ 2 ∈ Z) (hbZ : b ^ 2 ∈ Z)
    (haX : a ^ 2 ∈ X) (hbX : b ^ 2 ∉ X) (hNa : 2 * a ^ 2 ≤ N) (hNb : 2 * b ^ 2 ≤ N) :
    ∃ X' Y' : Finset ℕ, X'.Nonempty ∧
      (∀ n ∈ X', n ∈ X ∧ IsSquare n ∧ 1 < n) ∧ (∀ n ∈ Y', n ∉ X ∧ IsSquare n ∧ 1 < n) ∧
      ∑ n ∈ X', (1 : ℝ) / n = ∑ n ∈ Y', (1 : ℝ) / n := by
  classical
  let w := fun A : Finset ℕ => ∑ n ∈ A, (1 : ℝ) / n
  let s := fun n : ℕ => n ^ 2
  let t := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2
  let F := (range (N ^ 2)).filter (fun n => 2 ≤ n ∧ s n ∈ E)
  let Y := Z.filter (fun n => 1 < n ∧ n ∉ X)
  let R := w (Z \ E)
  have hY (n : ℕ) : n ∈ Y ↔ n ∈ Z ∧ 1 < n ∧ n ∉ X := mem_filter
  have hF (n : ℕ) : n ∈ F ↔ n < N ^ 2 ∧ 2 ≤ n ∧ s n ∈ E := by
    simp only [F, mem_filter, mem_range]
  have wmono {P U : Finset ℕ} (h : P ⊆ U) : w P ≤ w U :=
    sum_le_sum_of_subset_of_nonneg h fun i _ _ => by positivity
  have wun {P U : Finset ℕ} (h : Disjoint P U) : w (P ∪ U) = w P + w U := sum_union h
  have wimg (P : Finset ℕ) : w (P.image s) = ∑ n ∈ P, t n := by
    dsimp only [w, s, t]
    rw [sum_image (fun x _ y _ h => Nat.pow_left_injective (by decide) h)]
    simp only [Nat.cast_pow]
  have himg {P : Finset ℕ} (hP : P ⊆ F) : P.image s ⊆ E := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    exact ((hF n).mp (hP hn)).2.2
  have hdis {P U : Finset ℕ} (hP : P ⊆ E) (hU : U ⊆ Z \ E) : Disjoint P U :=
    disjoint_left.mpr fun _ hp hu => (mem_sdiff.mp (hU hu)).2 (hP hp)
  have wcover {P : Finset ℕ} (hP : P ⊆ F) :
      w (P.image s ∪ (Z \ E)) = (∑ n ∈ P, t n) + R := by
    rw [wun (hdis (himg hP) Subset.rfl), wimg]
  have hroot {z : ℕ} (hz : z ∈ E) (h1 : z ≠ 1) : ∃ n ∈ F, s n = z := by
    obtain ⟨n, hn, hNn, rfl⟩ := (hEsq z hz).resolve_left h1
    exact ⟨n, (hF n).mpr ⟨by omega, hn, hz⟩, rfl⟩
  have htot {P : Finset ℕ} (hP : P ⊆ Z) (h1 : 1 ∉ P) : w P ≤ (∑ n ∈ F, t n) + R := by
    rw [← wcover (P := F) Subset.rfl]
    apply wmono
    intro z hz
    by_cases he : z ∈ E
    · exact mem_union_left _ (mem_image.mpr (hroot he (fun hz1 => h1 (hz1 ▸ hz))))
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hP hz, he⟩)
  have hRpos : 0 < R := by
    apply Finset.sum_pos
    · intro d hd
      have hd0 := (hZsq d (mem_sdiff.mp hd).1).2
      positivity
    · exact hDne
  have hRle : R ≤ 2 / ((N : ℝ) + 1) := sum_squares_le N (Z \ E) fun d hd =>
    ⟨(hZsq d (mem_sdiff.mp hd).1).1, hD d hd⟩
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hR1 : R < 1 := hRle.trans_lt ((div_lt_iff₀ (by positivity)).mpr (by linarith only [hNreal]))
  have hsmall (u : ℕ) (hu : 2 ≤ u) (hNu : 2 * u ^ 2 ≤ N) : R ≤ (1 : ℝ) / (u ^ 2 : ℕ) := by
    have hh : (2 : ℝ) * (↑(u ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNu
    have hu0 : 0 < (u ^ 2 : ℕ) := pow_pos (by omega) _
    exact hRle.trans ((div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith only [hh]))
  have hstep (d : ℕ) (hd : d ∈ F) : t d ≤ (1 / (1 + 1 / 100) - 1 / 100) *
      ((∑ e ∈ F.filter (fun e => d < e), t e) + R) := by
    obtain ⟨hdN, hd2, _⟩ := (hF d).mp hd
    have hl := mass_above Z _ hmass d (by omega)
    have hc : Z.filter (fun z => d ^ 2 < z) ⊆ (F.filter (fun e => d < e)).image s ∪ (Z \ E) := by
      intro z hz
      obtain ⟨hzZ, hzgt⟩ := mem_filter.mp hz
      by_cases he : z ∈ E
      · obtain ⟨e, heF, rfl⟩ := hroot he (by intro h; subst z; nlinarith)
        change d ^ 2 < e ^ 2 at hzgt
        have hde : d < e := by
          by_contra! h
          exact hzgt.not_ge (Nat.pow_le_pow_left h 2)
        exact mem_union_left _ (mem_image.mpr ⟨e, mem_filter.mpr ⟨heF, hde⟩, rfl⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hzZ, he⟩)
    have hle := (wmono hc).trans_eq (wcover (filter_subset _ _))
    exact (num_ineq d N hd2 (by omega)).trans
      (mul_le_mul_of_nonneg_left (hl.trans hle) (by norm_num))
  have hYsub : Y ⊆ Z := filter_subset _ _
  have hbY : b ^ 2 ∈ Y := (hY _).mpr ⟨hbZ, by nlinarith, hbX⟩
  have haY : a ^ 2 ∉ Y := fun h => ((hY _).mp h).2.2 haX
  have hlow : 1 / 100 * R ≤ w Y := by
    have hh := wmono (singleton_subset_iff.mpr hbY)
    have hv : (1 : ℝ) / (b ^ 2 : ℕ) ≤ w Y := by simpa only [w, sum_singleton] using hh
    linarith only [hv, hsmall b hb hNb, hRpos]
  have hhigh : w Y ≤ (∑ n ∈ F, t n) + R / (1 + 1 / 100) := by
    have hh := htot (P := insert (a ^ 2) Y) (insert_subset haZ hYsub) (by
      intro h
      rcases mem_insert.mp h with h | h
      · nlinarith
      · have := ((hY 1).mp h).2.1
        omega)
    have hi : w (insert (a ^ 2) Y) = (1 : ℝ) / (a ^ 2 : ℕ) + w Y := sum_insert haY
    rw [hi] at hh
    have hdiv : 0 ≤ R / (1 + 1 / 100) := by positivity
    linarith only [hh, hsmall a ha hNa, hdiv]
  obtain ⟨P, hP, hqlo, hqhi⟩ := greedy t R (1 / 100) (by norm_num) hRpos.le F
    (fun d _ => by dsimp [t]; positivity) hstep (w Y) hlow hhigh
  let S := P.image s
  have hS : S ⊆ E := himg hP
  have hSw : w S = ∑ n ∈ P, t n := wimg P
  rw [← hSw] at hqlo hqhi
  have hqmul := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 + 1 / 100)).mp hqhi
  obtain ⟨D₁, D₂, hD₁, hD₂, h12, hk₁, hk₂⟩ := hcirc Y hYsub S hS
    (show 101 / 100 * (w Y - w S) ≤ R by linarith only [hqmul])
    (show R ≤ 100 * (w Y - w S) by linarith only [hqlo])
  have hqpos : 0 < w Y - w S := by linarith only [hqlo, hRpos]
  have hq1 : w Y - w S < 1 := by linarith only [hqmul, hR1]
  have hkzero {U : Finset ℕ} (hu : U ⊆ Z \ E) (hk : ∃ k : ℤ, w U = w Y - w S + k) :
      w U = w Y - w S := by
    obtain ⟨k, he⟩ := hk
    have hu0 : 0 ≤ w U := sum_nonneg fun i _ => by positivity
    have hu1 : w U < 1 := (wmono hu).trans_lt hR1
    have hl : (-1 : ℝ) < (k : ℝ) := by linarith only [hu0, he, hq1]
    have hh : (k : ℝ) < 1 := by linarith only [hu1, he, hqpos]
    have hl' : (-1 : ℤ) < k := by exact_mod_cast hl
    have hh' : k < (1 : ℤ) := by exact_mod_cast hh
    have hk' : k = 0 := by omega
    simpa [hk'] using he
  obtain ⟨U, hU, hne, hwU⟩ : ∃ U ⊆ Z \ E, U ≠ Y \ S ∧ w U = w Y - w S := by
    by_cases h : D₁ = Y \ S
    · exact ⟨D₂, hD₂, fun hh => h12 (h.trans hh.symm), hkzero hD₂ hk₂⟩
    · exact ⟨D₁, hD₁, h, hkzero hD₁ hk₁⟩
  have hSU := hdis hS hU
  apply split_of_two_subsets X Z (S ∪ U) Y hZsq hY
  · exact union_subset (hS.trans hEZ) (hU.trans sdiff_subset)
  · intro h
    rcases mem_union.mp h with hs | hu
    · obtain ⟨n, hn, hsq⟩ := mem_image.mp hs
      have := ((hF n).mp (hP hn)).2.1
      change n ^ 2 = 1 at hsq
      nlinarith
    · exact (mem_sdiff.mp (hU hu)).2 h1E
  · intro h
    apply hne
    rw [← h]
    ext n
    simp only [mem_sdiff, mem_union]
    constructor
    · intro hn
      exact ⟨Or.inr hn, fun hs => disjoint_left.mp hSU hs hn⟩
    · rintro ⟨hs | hu, hn⟩
      · exact False.elim (hn hs)
      · exact hu
  · change w (S ∪ U) = w Y
    rw [wun hSU, hwU]
    ring

theorem main : H1 → H2 → type_of% @Erdos318.erdos_318.parts.ii := by
  intro h1 h2
  apply p1_of_core
  intro X a b ha hb haX hbX
  obtain ⟨N₀, hN₀⟩ := h1
  obtain ⟨N₁, hN₁⟩ := h2
  obtain ⟨A, hA⟩ : ∃ A, A = a ^ 2 := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A', A' = b ^ 2 := ⟨_, rfl⟩
  have haA : a ≤ A := by rw [hA]; nlinarith
  have hbA : b ≤ A' := by rw [hA']; nlinarith
  have hc := hN₀ (N₀ + N₁ + 2 * A + 2 * A' + 2) (by omega)
  have hm := hN₁ (N₀ + N₁ + 2 * A + 2 * A' + 2) (by omega)
  obtain ⟨hZsq, hEZ, h1E, hEsq, hD, hDne, hsq⟩ :=
    Zstruct (N₀ + N₁ + 2 * A + 2 * A' + 2) (by omega) _ _ _ _ rfl rfl rfl rfl
  exact assemble (N₀ + N₁ + 2 * A + 2 * A' + 2) (by omega) _ _ hZsq hEZ h1E hEsq hD hDne hc hm
    X a b ha hb (hsq a ha (by omega)) (hsq b hb (by omega)) haX hbX (by omega) (by omega)

end OMA.R_Erdos318_erdos_318_parts_ii_R1
