import OMAStatements.S_erdos_791

/-!
Disproof of Erdős Problem 791: `g(n)/sqrt n` does not tend to `2`.

For `a b : ℕ` put `P = {i*a : i < b}`, `L = {0,...,a}`, `D = {a*b + s*(a+1) : s <= a}`,
`U = {2*a*b + r : r <= a}` and `Bas a b = P ∪ L ∪ D ∪ U`.  Its cardinality is at most
`b + 3a + 3`, and (`cover`) its sumset contains every integer up to `3ab + a^2 + 2a`.  With
`a = 3m`, `b = 7m` this gives `g(72m^2+6m) <= 16m+3`, so `g(n)/sqrt n <= 16/sqrt 72 < 2`
along that subsequence.
-/

namespace Erdos791

open Finset

/-- The candidate 2-basis with parameters `a`, `b`. -/
def Bas (a b : ℕ) : Finset ℕ :=
  (range b).image (fun i => i * a) ∪
    (range (a + 1) ∪
      ((range (a + 1)).image (fun s => a * b + s * (a + 1)) ∪
        (range (a + 1)).image (fun r => 2 * (a * b) + r)))

lemma mem_ap {a b i : ℕ} (hi : i < b) : i * a ∈ Bas a b :=
  mem_union.mpr (Or.inl (mem_image_of_mem _ (mem_range.mpr hi)))

lemma mem_low {a b r : ℕ} (hr : r ≤ a) : r ∈ Bas a b :=
  mem_union.mpr (Or.inr (mem_union.mpr (Or.inl (mem_range.mpr (by omega)))))

lemma mem_stair {a b s : ℕ} (hs : s ≤ a) : a * b + s * (a + 1) ∈ Bas a b :=
  mem_union.mpr (Or.inr (mem_union.mpr (Or.inr (mem_union.mpr
    (Or.inl (mem_image_of_mem _ (mem_range.mpr (by omega))))))))

lemma mem_top {a b r : ℕ} (hr : r ≤ a) : 2 * (a * b) + r ∈ Bas a b :=
  mem_union.mpr (Or.inr (mem_union.mpr (Or.inr (mem_union.mpr
    (Or.inr (mem_image_of_mem _ (mem_range.mpr (by omega))))))))

lemma card_Bas (a b : ℕ) : (Bas a b).card ≤ b + 3 * a + 3 := by
  have hP : ((range b).image (fun i => i * a)).card ≤ b :=
    le_trans card_image_le (le_of_eq (card_range b))
  have hL : (range (a + 1)).card = a + 1 := card_range (a + 1)
  have hD : ((range (a + 1)).image (fun s => a * b + s * (a + 1))).card ≤ a + 1 :=
    le_trans card_image_le (le_of_eq (card_range (a + 1)))
  have hU : ((range (a + 1)).image (fun r => 2 * (a * b) + r)).card ≤ a + 1 :=
    le_trans card_image_le (le_of_eq (card_range (a + 1)))
  have h1 : (Bas a b).card ≤ ((range b).image (fun i => i * a)).card +
      ((range (a + 1)) ∪ ((range (a + 1)).image (fun s => a * b + s * (a + 1)) ∪
        (range (a + 1)).image (fun r => 2 * (a * b) + r))).card := card_union_le _ _
  have h2 : ((range (a + 1)) ∪ ((range (a + 1)).image (fun s => a * b + s * (a + 1)) ∪
        (range (a + 1)).image (fun r => 2 * (a * b) + r))).card ≤
      (a + 1) + (((range (a + 1)).image (fun s => a * b + s * (a + 1)) ∪
        (range (a + 1)).image (fun r => 2 * (a * b) + r))).card :=
    le_trans (card_union_le _ _) (by omega)
  have h3 : (((range (a + 1)).image (fun s => a * b + s * (a + 1)) ∪
        (range (a + 1)).image (fun r => 2 * (a * b) + r))).card ≤ (a + 1) + (a + 1) :=
    le_trans (card_union_le _ _) (by omega)
  omega

/-- Every element of `Bas a b` is at most `2ab + a`. -/
lemma le_top_Bas {a b x : ℕ} (hab : a ≤ b) (hx : x ∈ Bas a b) : x ≤ 2 * (a * b) + a := by
  rcases mem_union.mp hx with h | h
  · rcases mem_image.mp h with ⟨i, hi, rfl⟩
    rw [mem_range] at hi
    have h1 : i * a ≤ (b - 1) * a := Nat.mul_le_mul_right a (by omega)
    have h2 : (b - 1) * a ≤ b * a := Nat.mul_le_mul_right a (by omega)
    nlinarith
  · rcases mem_union.mp h with h | h
    · rw [mem_range] at h; omega
    · rcases mem_union.mp h with h | h
      · rcases mem_image.mp h with ⟨s, hs, rfl⟩
        rw [mem_range] at hs
        have h1 : s * (a + 1) ≤ a * (a + 1) := Nat.mul_le_mul_right _ (by omega)
        have h2 : a * (a + 1) = a * a + a := by ring
        nlinarith
      · rcases mem_image.mp h with ⟨r, hr, rfl⟩
        rw [mem_range] at hr; omega

/-- Below `ab + a^2 + 2a` every number is `r + y` with `r <= a` and `y` in the basis. -/
lemma key {a b w : ℕ} (ha : 1 ≤ a) (hw : w ≤ a * b + a * a + 2 * a) :
    ∃ r : ℕ, r ≤ a ∧ ∃ y ∈ Bas a b, r + y = w := by
  have ha0 : 0 < a := by omega
  rcases Nat.lt_or_ge w (a * b) with hlt | hge
  · have hmod : w % a ≤ a := by have h := Nat.mod_lt w ha0; omega
    have hdiv : w / a < b := by
      rw [Nat.div_lt_iff_lt_mul ha0, Nat.mul_comm b a]
      exact hlt
    refine ⟨w % a, hmod, (w / a) * a, mem_ap hdiv, ?_⟩
    have hdm : a * (w / a) + w % a = w := Nat.div_add_mod w a
    rw [Nat.mul_comm a (w / a)] at hdm
    omega
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hge
    have hu : u ≤ a * a + 2 * a := by omega
    have hmod : u % (a + 1) ≤ a := by
      have h := Nat.mod_lt u (show 0 < a + 1 by omega); omega
    have hlt2 : u < (a + 1) * (a + 1) := by
      have h2 : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
      nlinarith
    have hdiv : u / (a + 1) ≤ a := by
      have h3 : u / (a + 1) < a + 1 := by
        rw [Nat.div_lt_iff_lt_mul (show 0 < a + 1 by omega)]
        exact hlt2
      omega
    refine ⟨u % (a + 1), hmod, a * b + (u / (a + 1)) * (a + 1), mem_stair hdiv, ?_⟩
    have hdm : (a + 1) * (u / (a + 1)) + u % (a + 1) = u := Nat.div_add_mod u (a + 1)
    rw [Nat.mul_comm (a + 1) (u / (a + 1))] at hdm
    omega

/-- The basis covers everything up to `3ab + a^2 + 2a`. -/
lemma cover {a b v : ℕ} (ha : 1 ≤ a) (hv : v ≤ 3 * (a * b) + a * a + 2 * a) :
    ∃ x ∈ Bas a b, ∃ y ∈ Bas a b, x + y = v := by
  have ha0 : 0 < a := by omega
  rcases Nat.lt_or_ge v (a * b + a * a + 2 * a) with h1 | h1
  · obtain ⟨r, hr, y, hy, hsum⟩ := key ha (le_of_lt h1)
    exact ⟨r, mem_low hr, y, hy, hsum⟩
  · rcases Nat.lt_or_ge v (2 * (a * b)) with h2 | h2
    · have habv : a * b ≤ v := by omega
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le habv
      have hu_gt : a * a + 2 * a ≤ u := by omega
      have hu_lt : u < a * b := by omega
      have hqa : a ≤ u / a := by
        rw [Nat.le_div_iff_mul_le ha0]
        omega
      have hmod : u % a ≤ a := by
        have h := Nat.mod_lt u ha0; omega
      have hqrm : u % a ≤ u / a := by
        have h := Nat.mod_lt u ha0; omega
      have hmul : (u % a) * a ≤ (u / a) * a := Nat.mul_le_mul_right a hqrm
      have hq' : u / a - u % a < b := by
        have hlt' : u / a < b := by
          rw [Nat.div_lt_iff_lt_mul ha0, Nat.mul_comm b a]
          exact hu_lt
        omega
      refine ⟨a * b + (u % a) * (a + 1), mem_stair hmod,
        (u / a - u % a) * a, mem_ap hq', ?_⟩
      have hdm : a * (u / a) + u % a = u := Nat.div_add_mod u a
      have hdm2 : (u / a) * a + u % a = u := by
        rw [Nat.mul_comm]; exact hdm
      have hsm : (u / a - u % a) * a = (u / a) * a - (u % a) * a := Nat.sub_mul _ _ _
      have hsplit : (u % a) * (a + 1) = (u % a) * a + (u % a) := by ring
      rw [hsm, hsplit]
      omega
    · obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le h2
      have hw : w ≤ a * b + a * a + 2 * a := by omega
      obtain ⟨r, hr, y, hy, hsum⟩ := key ha hw
      exact ⟨2 * (a * b) + r, mem_top hr, y, hy, by omega⟩

/-- The basis lies in `{0, ..., n}`. -/
lemma sub_Bas {a b n : ℕ} (hab : a ≤ b) (hn : 2 * (a * b) + a ≤ n) : Bas a b ⊆ range (n + 1) := by
  intro x hx
  rw [mem_range]
  have h := le_top_Bas hab hx
  omega

end Erdos791

theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_791.main) := by
  intro hmain
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (191 / 100 : ℝ) < (OMA.S_erdos_791.g n : ℝ) / Real.sqrt n := by
    apply hmain.eventually
    exact Ioi_mem_nhds (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  set m : ℕ := max M 100 with hm
  have hMle : M ≤ m := le_max_left _ _
  have hm100 : 100 ≤ m := le_max_right _ _
  have hm' : (100 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm100
  have hcov : ∀ v ≤ 72 * m ^ 2 + 6 * m,
      ∃ x ∈ Erdos791.Bas (3 * m) (7 * m), ∃ y ∈ Erdos791.Bas (3 * m) (7 * m), x + y = v := by
    intro v hv
    have heq : 3 * ((3 * m) * (7 * m)) + (3 * m) * (3 * m) + 2 * (3 * m) = 72 * m ^ 2 + 6 * m := by
      ring
    exact Erdos791.cover (ha := by omega) (by omega)
  have hsub : Erdos791.Bas (3 * m) (7 * m) ⊆ Finset.range (72 * m ^ 2 + 6 * m + 1) := by
    refine Erdos791.sub_Bas (hab := by omega) ?_
    nlinarith
  have hg : OMA.S_erdos_791.g (72 * m ^ 2 + 6 * m) ≤ 16 * m + 3 := by
    have hmem : (Erdos791.Bas (3 * m) (7 * m)).card ∈
        {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.range (72 * m ^ 2 + 6 * m + 1) ∧ A.card = k ∧
          ∀ v ≤ 72 * m ^ 2 + 6 * m, ∃ a ∈ A, ∃ b ∈ A, a + b = v} :=
      ⟨Erdos791.Bas (3 * m) (7 * m), hsub, rfl, hcov⟩
    have h1 : OMA.S_erdos_791.g (72 * m ^ 2 + 6 * m) ≤ (Erdos791.Bas (3 * m) (7 * m)).card :=
      Nat.sInf_le hmem
    have h2 : (Erdos791.Bas (3 * m) (7 * m)).card ≤ 7 * m + 3 * (3 * m) + 3 :=
      Erdos791.card_Bas (3 * m) (7 * m)
    omega
  have hNpos : (0 : ℝ) < Real.sqrt ((72 * m ^ 2 + 6 * m : ℕ) : ℝ) := by
    rw [Real.sqrt_pos]
    have hpos : (0 : ℕ) < 72 * m ^ 2 + 6 * m := by nlinarith
    exact_mod_cast hpos
  have hgle : (OMA.S_erdos_791.g (72 * m ^ 2 + 6 * m) : ℝ) ≤ ((16 * m + 3 : ℕ) : ℝ) := by
    exact_mod_cast hg
  have hstep : ((16 * m + 3 : ℕ) : ℝ) ≤ (191 / 100 : ℝ) * Real.sqrt ((72 * m ^ 2 + 6 * m : ℕ) : ℝ) := by
    have hx : (0 : ℝ) < (100 / 191 : ℝ) * ((16 * m + 3 : ℕ) : ℝ) := by
      have h1 : (0 : ℝ) < ((16 * m + 3 : ℕ) : ℝ) := by
        have h2 : (0 : ℕ) < 16 * m + 3 := by omega
        exact_mod_cast h2
      positivity
    have hsq : ((100 / 191 : ℝ) * ((16 * m + 3 : ℕ) : ℝ)) ^ 2 ≤ ((72 * m ^ 2 + 6 * m : ℕ) : ℝ) := by
      push_cast
      nlinarith [sq_nonneg ((m : ℝ) - 100)]
    have hle := (Real.le_sqrt' (x := (100 / 191 : ℝ) * ((16 * m + 3 : ℕ) : ℝ))
      (y := ((72 * m ^ 2 + 6 * m : ℕ) : ℝ)) hx).mpr hsq
    nlinarith
  have hbound : (OMA.S_erdos_791.g (72 * m ^ 2 + 6 * m) : ℝ) /
      Real.sqrt ((72 * m ^ 2 + 6 * m : ℕ) : ℝ) ≤ 191 / 100 := by
    calc (OMA.S_erdos_791.g (72 * m ^ 2 + 6 * m) : ℝ) / Real.sqrt ((72 * m ^ 2 + 6 * m : ℕ) : ℝ)
        ≤ ((16 * m + 3 : ℕ) : ℝ) / Real.sqrt ((72 * m ^ 2 + 6 * m : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hgle (le_of_lt hNpos)
      _ ≤ 191 / 100 := by
          rw [div_le_iff₀ hNpos]
          linarith
  have hMN : M ≤ 72 * m ^ 2 + 6 * m := by
    have h1 : m ≤ 6 * m := by omega
    have h2 : 6 * m ≤ 72 * m ^ 2 + 6 * m := Nat.le_add_left (6 * m) (72 * m ^ 2)
    exact le_trans hMle (le_trans h1 h2)
  have hcontra := hM (72 * m ^ 2 + 6 * m) hMN
  linarith [hbound, hcontra]
