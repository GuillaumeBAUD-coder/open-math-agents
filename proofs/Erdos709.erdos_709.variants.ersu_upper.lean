import FormalConjectures.ErdosProblems.«709»

-- Problem: Erdős Problem 709 — ersu upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/709.lean:197 (declaration Erdos709.erdos_709.variants.ersu_upper)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Asymptotics Finset

namespace OMA709

open Erdos709

/-- One run of `2 M` consecutive integers holds distinct multiples of at least `√ #A`
elements of `A` (Erdős and Surányi, Section 11). -/
lemma run (A : Finset ℕ) (M start : ℕ) (hA : ∀ a ∈ A, 0 < a ∧ a ≤ M) :
    ∃ B ⊆ A, ∃ c : ℕ → ℕ, Set.InjOn c (B : Set ℕ) ∧
      (∀ a ∈ B, c a ∈ window start (2 * M) ∧ a ∣ c a) ∧ #A ≤ #B * #B := by
  have hhit : ∀ a ∈ A, ∃ x ∈ window start (2 * M), a ∣ x := fun a ha =>
    exists_multiple_in_window a (2 * M) start (hA a ha).1 (by have := (hA a ha).2; omega)
  let H := (window start (2 * M)).powerset.filter (fun X => ∀ a ∈ A, ∃ x ∈ X, a ∣ x)
  have hHne : H.Nonempty :=
    ⟨window start (2 * M), Finset.mem_filter.2 ⟨Finset.mem_powerset.2 subset_rfl, hhit⟩⟩
  obtain ⟨X, hXH, hXmin⟩ := Finset.exists_min_image H Finset.card hHne
  rw [Finset.mem_filter, Finset.mem_powerset] at hXH
  obtain ⟨hXw, hXhit⟩ := hXH
  let c : ℕ → ℕ := fun a => if h : a ∈ A then Classical.choose (hXhit a h) else 0
  have hc : ∀ a ∈ A, c a ∈ X ∧ a ∣ c a := by
    intro a ha
    simp only [c, dif_pos ha]
    exact Classical.choose_spec (hXhit a ha)
  have hpriv : ∀ x ∈ X, ∃ a ∈ A, a ∣ x ∧ ∀ y ∈ X, a ∣ y → y = x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hmem : X.erase x ∈ H := by
      refine Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 ((Finset.erase_subset _ _).trans hXw), ?_⟩
      intro a ha
      obtain ⟨y, hy, hay⟩ := hXhit a ha
      by_cases hyx : y = x
      · subst hyx
        obtain ⟨z, hz, haz, hzx⟩ := hcon a ha hay
        exact ⟨z, Finset.mem_erase.2 ⟨hzx, hz⟩, haz⟩
      · exact ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, hay⟩
    have h1 := hXmin _ hmem
    have h2 := Finset.card_erase_lt_of_mem hx
    omega
  choose! p hpA hpdvd hpuniq using hpriv
  have hcp : ∀ x ∈ X, c (p x) = x := fun x hx =>
    hpuniq x hx _ (hc _ (hpA x hx)).1 (hc _ (hpA x hx)).2
  have hpinj : Set.InjOn p (X : Set ℕ) := by
    intro x hx y hy hxy
    rw [← hcp x hx, ← hcp y hy, hxy]
  have hB1card : #(X.image p) = #X := Finset.card_image_of_injOn hpinj
  have hB1 : X.image p ⊆ A := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    exact hpA x hx
  have hB1inj : Set.InjOn c ((X.image p : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [hcp x hx, hcp y hy] at hab
    rw [hab]
  have hB1prop : ∀ a ∈ X.image p, c a ∈ window start (2 * M) ∧ a ∣ c a := by
    intro a ha
    have haA := hB1 ha
    exact ⟨hXw (hc a haA).1, (hc a haA).2⟩
  rcases X.eq_empty_or_nonempty with hX0 | hXne
  · have hA0 : A = ∅ := by
      ext a
      simp only [Finset.notMem_empty, iff_false]
      intro ha
      have := (hc a ha).1
      rw [hX0] at this
      simp at this
    refine ⟨∅, by simp, c, by simp, by simp, by simp [hA0]⟩
  obtain ⟨x, hx, hxmax⟩ :=
    Finset.exists_max_image X (fun x => #(A.filter (fun a => c a = x))) hXne
  set F := A.filter (fun a => c a = x) with hF
  have hsum : #A = ∑ y ∈ X, #(A.filter (fun a => c a = y)) :=
    Finset.card_eq_sum_card_fiberwise (fun a ha => (hc a ha).1)
  have hAle : #A ≤ #X * #F := by
    rw [hsum]
    calc ∑ y ∈ X, #(A.filter (fun a => c a = y)) ≤ ∑ y ∈ X, #F :=
          Finset.sum_le_sum (fun y hy => hxmax y hy)
      _ = #X * #F := by rw [Finset.sum_const, smul_eq_mul]
  have hxw := hXw hx
  simp only [window, Finset.mem_Icc] at hxw
  let c2 : ℕ → ℕ := fun a => if x ≤ start + M then x + a else x - a
  have hFdvd : ∀ a ∈ F, a ∣ x := fun a ha => by
    rw [hF, Finset.mem_filter] at ha
    have := (hc a ha.1).2
    rw [ha.2] at this
    exact this
  have hFinj : Set.InjOn c2 (F : Set ℕ) := by
    intro a ha b hb hab
    have hal := (hA a (Finset.mem_filter.1 ha).1).2
    have hbl := (hA b (Finset.mem_filter.1 hb).1).2
    simp only [c2] at hab
    split_ifs at hab <;> omega
  have hFprop : ∀ a ∈ F, c2 a ∈ window start (2 * M) ∧ a ∣ c2 a := by
    intro a ha
    have haA := (Finset.mem_filter.1 ha).1
    have hal := hA a haA
    have hdx := hFdvd a ha
    simp only [c2, window, Finset.mem_Icc]
    split_ifs with h
    · exact ⟨⟨by omega, by omega⟩, Nat.dvd_add hdx dvd_rfl⟩
    · exact ⟨⟨by omega, by omega⟩, Nat.dvd_sub hdx dvd_rfl⟩
  by_cases hk : #F ≤ #X
  · refine ⟨X.image p, hB1, c, hB1inj, hB1prop, ?_⟩
    rw [hB1card]
    exact hAle.trans (Nat.mul_le_mul_left _ hk)
  · refine ⟨F, Finset.filter_subset _ _, c2, hFinj, hFprop, ?_⟩
    exact hAle.trans (Nat.mul_le_mul_right _ (by omega))

/-- Iterating the run lemma over `t` runs with `4 #A ≤ t²` serves every element. -/
lemma iter (M : ℕ) : ∀ n, ∀ A : Finset ℕ, #A = n → (∀ a ∈ A, 0 < a ∧ a ≤ M) →
    ∀ t start, 4 * n ≤ t * t → HasDistinctMultiples A start (2 * M * t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAn hA t start ht
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : A = ∅ := Finset.card_eq_zero.1 hAn
    subst this
    exact ⟨id, by simp, by simp⟩
  obtain ⟨B, hBA, c, hcinj, hcB, hcard⟩ := run A M start hA
  have hBn : #B ≤ n := hAn ▸ Finset.card_le_card hBA
  have hBpos : 0 < #B := by
    rcases Nat.eq_zero_or_pos #B with h | h
    · rw [h] at hcard; omega
    · exact h
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; omega
    · exact h
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hsd : #(A \ B) = n - #B := by rw [Finset.card_sdiff_of_subset hBA, hAn]
  have hlt : n - #B < n := by omega
  have ht' : 4 * (n - #B) ≤ s * s := by
    rcases le_or_gt (s + 1) (2 * #B) with h | h
    · have e : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
      rw [e] at ht
      generalize s * s = q at ht ⊢
      omega
    · have h2 : 2 * #B ≤ s := by omega
      calc 4 * (n - #B) ≤ 4 * n := by omega
        _ ≤ 4 * (#B * #B) := by omega
        _ = (2 * #B) * (2 * #B) := by ring
        _ ≤ s * s := Nat.mul_le_mul h2 h2
  obtain ⟨c', hc'inj, hc'⟩ := ih (n - #B) hlt (A \ B) hsd
    (fun a ha => hA a (Finset.mem_sdiff.1 ha).1) s (start + 2 * M) ht'
  have e2 : 2 * M * (s + 1) = 2 * M + 2 * M * s := by ring
  refine ⟨fun a => if a ∈ B then c a else c' a, ?_, ?_⟩
  · intro a ha b hb hab
    simp only at hab
    by_cases haB : a ∈ B <;> by_cases hbB : b ∈ B <;>
      simp only [haB, hbB, if_true, if_false] at hab
    · exact hcinj haB hbB hab
    · exfalso
      have h1 := (hcB a haB).1
      have h2 := (hc' b (Finset.mem_sdiff.2 ⟨hb, hbB⟩)).1
      simp only [window, Finset.mem_Icc] at h1 h2
      omega
    · exfalso
      have h1 := (hcB b hbB).1
      have h2 := (hc' a (Finset.mem_sdiff.2 ⟨ha, haB⟩)).1
      simp only [window, Finset.mem_Icc] at h1 h2
      omega
    · exact hc'inj (Finset.mem_sdiff.2 ⟨ha, haB⟩) (Finset.mem_sdiff.2 ⟨hb, hbB⟩) hab
  · intro a ha
    by_cases haB : a ∈ B
    · simp only [haB, if_true]
      obtain ⟨h1, h2⟩ := hcB a haB
      refine ⟨?_, h2⟩
      simp only [window, Finset.mem_Icc] at h1 ⊢
      rw [e2]
      omega
    · simp only [haB, if_false]
      obtain ⟨h1, h2⟩ := hc' a (Finset.mem_sdiff.2 ⟨ha, haB⟩)
      refine ⟨?_, h2⟩
      simp only [window, Finset.mem_Icc] at h1 ⊢
      rw [e2]
      omega

lemma nonneg_of_admissible (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : IsAdmissible n c) : 0 ≤ c := by
  by_contra hneg
  push Not at hneg
  have hcard : #(Finset.Icc 2 (n + 1)) = n := by simp
  have h2 : ∀ a ∈ Finset.Icc 2 (n + 1), 2 ≤ a := fun a ha => (Finset.mem_Icc.1 ha).1
  have hle : c * (((Finset.Icc 2 (n + 1)).sup id : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) := by
    simp only [Nat.cast_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hneg.le (Nat.cast_nonneg _)
  obtain ⟨choice, _, hch⟩ := hc _ hcard h2 0 0 hle
  have hmem : 2 ∈ Finset.Icc 2 (n + 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have := (hch 2 hmem).1
  simp [window] at this

end OMA709

theorem OMA.solution : type_of% @Erdos709.erdos_709.variants.ersu_upper := by
  refine Asymptotics.IsBigO.of_bound 6 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hsq : (1 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hrp : (n : ℝ) ^ (1 / 2 : ℝ) = √(n : ℝ) := (Real.sqrt_eq_rpow _).symm
  have hadm : Erdos709.IsAdmissible n (6 * √(n : ℝ)) := by
    intro A hAc hA2 start length hlen
    have hAM : ∀ a ∈ A, 0 < a ∧ a ≤ A.sup id := fun a ha =>
      ⟨by have := hA2 a ha; omega, Finset.le_sup (f := id) ha⟩
    have ht : 4 * n ≤ ⌈2 * √(n : ℝ)⌉₊ * ⌈2 * √(n : ℝ)⌉₊ := by
      have h1 : 2 * √(n : ℝ) ≤ (⌈2 * √(n : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
      have h2 : (4 * n : ℝ) ≤ (⌈2 * √(n : ℝ)⌉₊ : ℝ) * ⌈2 * √(n : ℝ)⌉₊ := by
        nlinarith [Real.sqrt_nonneg (n : ℝ)]
      exact_mod_cast h2
    have hlen' : 2 * (A.sup id) * ⌈2 * √(n : ℝ)⌉₊ ≤ length := by
      have h1 : (⌈2 * √(n : ℝ)⌉₊ : ℝ) < 2 * √(n : ℝ) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hM : (0 : ℝ) ≤ ((A.sup id : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : ((2 * (A.sup id) * ⌈2 * √(n : ℝ)⌉₊ : ℕ) : ℝ) ≤ length := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left h1.le hM, mul_le_mul_of_nonneg_left hsq hM]
      exact_mod_cast h2
    exact Erdos709.matching_mono_length A start _ _ hlen'
      (OMA709.iter (A.sup id) n A hAc hAM _ start ht)
  have hbdd : BddBelow {c : ℝ | Erdos709.IsAdmissible n c} :=
    ⟨0, fun c hc => OMA709.nonneg_of_admissible n hn c hc⟩
  have hle : Erdos709.f n ≤ 6 * √(n : ℝ) := csInf_le hbdd hadm
  have hge : 0 ≤ Erdos709.f n :=
    le_csInf ⟨_, hadm⟩ (fun c hc => OMA709.nonneg_of_admissible n hn c hc)
  rw [hrp, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg hge]
  exact hle
