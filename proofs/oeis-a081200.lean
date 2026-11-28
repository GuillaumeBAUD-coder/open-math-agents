import OMAStatements.S_oeis_a081200

-- Double-counting proof: every collinear 5-subset of the 5^n grid is the image of a word in which
-- each coordinate is constant or runs through 0..4 upwards or downwards, with at least one
-- moving coordinate; exactly two words (a word and its reversal) give each line, and there are
-- 7^n - 5^n such words.
-- The argument follows the accepted proof of the template entry OEIS A081201 (with 5 in place of 6).
-- Mathlib's Collinear is first reduced to the vanishing of all two-coordinate minors.

namespace OMA.P_a081200

open OMA.S_oeis_a081200

abbrev Grid (n : ℕ) := Fin n → Fin 5

/-- Every displacement from a fixed point is parallel to the line through two
distinct points of the set. All two-coordinate minors are computed in ℤ. -/
def MinorCollinear {n : ℕ} (s : Finset (Grid n)) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∀ z ∈ s, ∀ i j : Fin n,
    ((z i : ℤ) - a i) * ((b j : ℤ) - a j) =
      ((z j : ℤ) - a j) * ((b i : ℤ) - a i)


private abbrev Symbol := Fin 5 ⊕ Bool
private abbrev Word (n : ℕ) := Fin n → Symbol

private def value : Symbol → Fin 5 → Fin 5
  | .inl a, _ => a
  | .inr true, t => t
  | .inr false, t => t.rev

private def slope : Symbol → ℤ
  | .inl _ => 0
  | .inr true => 1
  | .inr false => -1

private def point {n : ℕ} (w : Word n) (t : Fin 5) : Grid n :=
  fun i => value (w i) t

private def active {n : ℕ} (w : Word n) : Prop :=
  ∃ (i : Fin n) (b : Bool), w i = .inr b

private noncomputable def entries {n : ℕ} (w : Word n) : Finset (Grid n) := by
  classical
  exact Finset.univ.image (point w)

private theorem mem_entries {n : ℕ} {w : Word n} {p : Grid n} :
    p ∈ entries w ↔ ∃ t, point w t = p := by
  classical
  simp [entries]

private theorem cast_rev (t : Fin 5) : (t.rev : ℤ) = 4 - (t : ℤ) := by
  have ht := t.isLt
  simp only [Fin.val_rev]
  omega

private theorem value_affine (c : Symbol) (t : Fin 5) :
    (value c t : ℤ) = (value c 0 : ℤ) + (t : ℤ) * slope c := by
  rcases c with a | (_ | _)
  · simp [value, slope]
  · change (t.rev : ℤ) = ((0 : Fin 5).rev : ℤ) + (t : ℤ) * (-1)
    rw [cast_rev t, cast_rev (0 : Fin 5)]
    change 4 - (t : ℤ) = (4 - 0) + (t : ℤ) * (-1)
    ring
  · simp [value, slope]

private theorem value_active_injective (b : Bool) : Function.Injective (value (.inr b)) := by
  cases b <;> simp [value, Function.Injective]

private theorem symbol_injective :
    Function.Injective (fun c : Symbol => (value c 0, value c 4)) := by
  decide

private theorem entries_valid {n : ℕ} {w : Word n} (hw : active w) :
    (entries w).card = 5 ∧ MinorCollinear (entries w) := by
  classical
  obtain ⟨i, b, hi⟩ := hw
  have hp : Function.Injective (point w) := by
    intro u v h
    apply value_active_injective b
    simpa [point, hi] using congrFun h i
  constructor
  · simp [entries, Finset.card_image_of_injective _ hp]
  · refine ⟨point w 0, mem_entries.mpr ⟨0, rfl⟩, point w 1,
      mem_entries.mpr ⟨1, rfl⟩, fun h => (by decide : (0 : Fin 5) ≠ 1) (hp h), ?_⟩
    intro z hz j k
    obtain ⟨t, rfl⟩ := mem_entries.mp hz
    change ((value (w j) t : ℤ) - value (w j) 0) *
        ((value (w k) 1 : ℤ) - value (w k) 0) =
      ((value (w k) t : ℤ) - value (w k) 0) *
        ((value (w j) 1 : ℤ) - value (w j) 0)
    rw [value_affine (w j) t, value_affine (w k) t,
      value_affine (w j) 1, value_affine (w k) 1]
    ring

-- The values at parameters 0, 1, and 4 force the integral step to be 0 or ±1.
private theorem classify (a b c : Fin 5)
    (h : (c : ℤ) = (a : ℤ) + 4 * ((b : ℤ) - (a : ℤ))) :
    ∃ u : Symbol, ∀ t : Fin 5,
      (value u t : ℤ) = (a : ℤ) + (t : ℤ) * ((b : ℤ) - (a : ℤ)) := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  rcases lt_trichotomy (b : ℤ) (a : ℤ) with hlt | heq | hgt
  · refine ⟨.inr false, fun t => ?_⟩
    have hA : (a : ℤ) = 4 := by omega
    have hB : (b : ℤ) = 3 := by omega
    rw [hA, hB, show value (.inr false) t = t.rev from rfl, cast_rev]
    ring
  · refine ⟨.inl a, fun t => ?_⟩
    simp [value, heq]
  · refine ⟨.inr true, fun t => ?_⟩
    have hA : (a : ℤ) = 0 := by omega
    have hB : (b : ℤ) = 1 := by omega
    rw [hA, hB]
    change (t : ℤ) = 0 + (t : ℤ) * (1 - 0)
    ring

private theorem entries_surj {n : ℕ} {s : Finset (Grid n)}
    (hs : s.card = 5) (hl : MinorCollinear s) :
    ∃ w : Word n, active w ∧ entries w = s := by
  classical
  obtain ⟨a, _, b, _, hab, hline⟩ := hl
  have hsome : ∃ i, a i ≠ b i := by
    by_contra! h
    exact hab (funext h)
  obtain ⟨i, hi⟩ := hsome
  have hd : (b i : ℤ) - (a i : ℤ) ≠ 0 := by
    intro h
    apply hi
    exact Fin.ext (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have hproj : Set.InjOn (fun p : Grid n => p i) (s : Set (Grid n)) := by
    intro x hx y hy hxy
    funext j
    have he : (x i : ℤ) = (y i : ℤ) := congrArg (fun q : Fin 5 => (q : ℤ)) hxy
    have hm : ((x j : ℤ) - (y j : ℤ)) * ((b i : ℤ) - (a i : ℤ)) = 0 := by
      linear_combination hline x hx j i - hline y hy j i +
        ((b j : ℤ) - (a j : ℤ)) * he
    have hval := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hd)
    exact Fin.ext (by exact_mod_cast hval)
  have hfull : (s.image (fun p : Grid n => p i)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simp [Finset.card_image_of_injOn hproj, hs])
  have hp (t : Fin 5) : ∃ x ∈ s, x i = t := by
    apply Finset.mem_image.mp
    rw [hfull]
    exact Finset.mem_univ t
  obtain ⟨x₀, hx₀, hi₀⟩ := hp 0
  obtain ⟨x₁, hx₁, hi₁⟩ := hp 1
  obtain ⟨x₅, hx₅, hi₅⟩ := hp 4
  have h₀ : (x₀ i : ℤ) = 0 := by
    simpa using congrArg (fun t : Fin 5 => (t : ℤ)) hi₀
  have h₁ : (x₁ i : ℤ) = 1 := by
    simpa using congrArg (fun t : Fin 5 => (t : ℤ)) hi₁
  have h₅ : (x₅ i : ℤ) = 4 := by
    simpa using congrArg (fun t : Fin 5 => (t : ℤ)) hi₅
  have haff (z : Grid n) (hz : z ∈ s) (j : Fin n) :
      (z j : ℤ) = (x₀ j : ℤ) + (z i : ℤ) * ((x₁ j : ℤ) - (x₀ j : ℤ)) := by
    have h0 := hline x₀ hx₀ j i
    have h1 := hline x₁ hx₁ j i
    rw [h₀] at h0
    rw [h₁] at h1
    have hm : ((z j : ℤ) - ((x₀ j : ℤ) + (z i : ℤ) * ((x₁ j : ℤ) - (x₀ j : ℤ)))) *
        ((b i : ℤ) - (a i : ℤ)) = 0 := by
      linear_combination hline z hz j i - h0 - (z i : ℤ) * (h1 - h0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hd)
  have hc (j : Fin n) :
      ∃ u : Symbol, ∀ t : Fin 5,
        (value u t : ℤ) = (x₀ j : ℤ) + (t : ℤ) * ((x₁ j : ℤ) - (x₀ j : ℤ)) :=
    classify _ _ _ (by simpa [h₅] using haff x₅ hx₅ j)
  choose w hw using hc
  have he (z : Grid n) (hz : z ∈ s) : point w (z i) = z := by
    funext j
    exact Fin.ext (by exact_mod_cast (hw j (z i)).trans (haff z hz j).symm)
  refine ⟨w, ?_, ?_⟩
  · cases e : w i with
    | inl c =>
      have e₀ := congrFun (he x₀ hx₀) i
      have e₁ := congrFun (he x₁ hx₁) i
      simp [point, e, value, hi₀, hi₁] at e₀ e₁
      exact ((by decide : (0 : Fin 5) ≠ 1) (e₀.symm.trans e₁)).elim
    | inr b => exact ⟨i, b, e⟩
  · ext z
    rw [mem_entries]
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨y, hy, hiy⟩ := hp t
      have hyPoint : point w t = y := by simpa [hiy] using he y hy
      rwa [hyPoint]
    · intro hz
      exact ⟨z i, he z hz⟩

private def flip : Symbol → Symbol
  | .inl a => .inl a
  | .inr b => .inr (!b)

private def reverse {n : ℕ} (w : Word n) : Word n := fun i => flip (w i)

private theorem reverse_reverse {n : ℕ} (w : Word n) : reverse (reverse w) = w := by
  funext i
  rcases h : w i with a | b <;> simp [reverse, flip, h]

private theorem reverse_point {n : ℕ} (w : Word n) (t : Fin 5) :
    point (reverse w) t = point w t.rev := by
  funext i
  rcases h : w i with a | (_ | _) <;> simp [point, reverse, flip, value, h]

private theorem entries_reverse {n : ℕ} (w : Word n) : entries (reverse w) = entries w := by
  ext z
  simp only [mem_entries, reverse_point]
  exact ⟨fun ⟨t, ht⟩ => ⟨t.rev, ht⟩, fun ⟨t, ht⟩ => ⟨t.rev, by simpa using ht⟩⟩

private theorem reverse_active {n : ℕ} {w : Word n} (h : active w) : active (reverse w) := by
  obtain ⟨i, b, hb⟩ := h
  exact ⟨i, !b, by simp [reverse, flip, hb]⟩

private theorem reverse_ne {n : ℕ} {w : Word n} (h : active w) : w ≠ reverse w := by
  obtain ⟨i, b, hb⟩ := h
  intro he
  have hi := congrFun he i
  cases b <;> simp [reverse, flip, hb] at hi

private theorem entries_fiber {n : ℕ} {w v : Word n} (hw : active w)
    (hv : entries v = entries w) : v = w ∨ v = reverse w := by
  obtain ⟨i, b, hb⟩ := hw
  have h_aligned (u : Word n) (hu : entries u = entries w) (hi : u i = .inr b) : u = w := by
    have hp (t : Fin 5) : point u t = point w t := by
      have hm : point u t ∈ entries w := by
        rw [← hu]
        exact mem_entries.mpr ⟨t, rfl⟩
      obtain ⟨k, hk⟩ := mem_entries.mp hm
      have hkt : k = t := value_active_injective b (by simpa [point, hb, hi] using congrFun hk i)
      exact hkt ▸ hk.symm
    funext j
    exact symbol_injective (Prod.ext (congrFun (hp 0) j) (congrFun (hp 4) j))
  have hvar : ∃ c, v i = .inr c := by
    cases hi : v i with
    | inr c => exact ⟨c, rfl⟩
    | inl a =>
      have hp (t : Fin 5) : value (.inr b) t = a := by
        have hm : point w t ∈ entries v := by
          rw [hv]
          exact mem_entries.mpr ⟨t, rfl⟩
        obtain ⟨k, hk⟩ := mem_entries.mp hm
        simpa [point, hb, hi, value] using (congrFun hk i).symm
      exact ((by decide : (0 : Fin 5) ≠ 1)
        (value_active_injective b ((hp 0).trans (hp 1).symm))).elim
  obtain ⟨c, hc⟩ := hvar
  by_cases he : c = b
  · exact Or.inl (h_aligned v hv (by simpa [he] using hc))
  · right
    have hf : (!c) = b := by cases c <;> cases b <;> simp_all
    have hrev := h_aligned (reverse v) ((entries_reverse v).trans hv) (by
      change flip (v i) = .inr b
      rw [hc]
      exact congrArg Sum.inr hf)
    simpa only [reverse_reverse] using congrArg reverse hrev

private noncomputable def words (n : ℕ) : Finset (Word n) := by
  classical
  exact Finset.univ.filter active

private noncomputable def lines (n : ℕ) : Finset (Finset (Grid n)) := by
  classical
  exact Finset.univ.filter (fun s => s.card = 5 ∧ MinorCollinear s)

private theorem words_card (n : ℕ) : (words n).card = 7 ^ n - 5 ^ n := by
  classical
  let f : Grid n → Word n := fun a i => .inl (a i)
  have hf : Function.Injective f := by
    intro x y h
    funext i
    exact Sum.inl.inj (congrFun h i)
  have hrest : (Finset.univ.filter (fun w : Word n => ¬ active w)) =
      (Finset.univ : Finset (Grid n)).image f := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have hi (i : Fin n) : ∃ a : Fin 5, w i = .inl a := by
        cases e : w i with
        | inl a => exact ⟨a, rfl⟩
        | inr b => exact (h ⟨i, b, e⟩).elim
      choose a ha using hi
      exact ⟨a, funext fun i => (ha i).symm⟩
    · rintro ⟨a, rfl⟩ ⟨i, b, hb⟩
      cases hb
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Word n)))
    (p := active)
  rw [hrest, Finset.card_image_of_injective _ hf] at h
  simpa [words, Fintype.card_pi_const] using (Nat.eq_sub_of_add_eq h)

private theorem twice_lines (n : ℕ) : (words n).card = (lines n).card * 2 := by
  classical
  have hmap : ∀ w ∈ words n, entries w ∈ lines n := by
    intro w hw
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, entries_valid (Finset.mem_filter.mp hw).2⟩
  have htwo (s : Finset (Grid n)) (hs : s ∈ lines n) :
      ((words n).filter fun w => entries w = s).card = 2 := by
    have hls := (Finset.mem_filter.mp hs).2
    obtain ⟨w, hw, he⟩ := entries_surj hls.1 hls.2
    have hpair : ((words n).filter fun v => entries v = s) = {w, reverse w} := by
      ext v
      simp only [Finset.mem_filter, words, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨_, hv⟩
        exact entries_fiber hw (hv.trans he.symm)
      · rintro (rfl | rfl)
        · exact ⟨hw, he⟩
        · exact ⟨reverse_active hw, (entries_reverse w).trans he⟩
    rw [hpair]
    exact Finset.card_pair_eq_two_iff.mpr (reverse_ne hw)
  rw [Finset.card_eq_sum_card_fiberwise (f := entries) (t := lines n) hmap]
  calc
    _ = ∑ s ∈ lines n, (2 : ℕ) := Finset.sum_congr rfl htwo
    _ = _ := by simp


/-- Mathlib collinearity of the real image agrees with the minor condition on sets of size two
or more. -/
private theorem collinear_iff_minor {n : ℕ} (s : Finset (Grid n)) (hs : 2 ≤ s.card) :
    _root_.Collinear ℝ (toReal '' (s : Set (Grid n))) ↔ MinorCollinear s := by
  classical
  constructor
  · intro hc
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    rw [collinear_iff_of_mem (p₀ := toReal a) (Set.mem_image_of_mem toReal (Finset.mem_coe.mpr ha))] at hc
    obtain ⟨v, hv⟩ := hc
    refine ⟨a, ha, b, hb, hab, fun z hz i j => ?_⟩
    obtain ⟨rz, hrz⟩ := hv _ ⟨z, hz, rfl⟩
    obtain ⟨rb, hrb⟩ := hv _ ⟨b, hb, rfl⟩
    have hzi := congrFun hrz i
    have hzj := congrFun hrz j
    have hbi := congrFun hrb i
    have hbj := congrFun hrb j
    simp only [toReal, vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzi hzj hbi hbj
    have key : (((z i : ℕ) : ℝ) - ((a i : ℕ) : ℝ)) * (((b j : ℕ) : ℝ) - ((a j : ℕ) : ℝ)) =
        (((z j : ℕ) : ℝ) - ((a j : ℕ) : ℝ)) * (((b i : ℕ) : ℝ) - ((a i : ℕ) : ℝ)) := by
      rw [hzi, hzj, hbi, hbj]; ring
    exact_mod_cast key
  · rintro ⟨a, ha, b, hb, hab, hline⟩
    rw [collinear_iff_of_mem (p₀ := toReal a) (Set.mem_image_of_mem toReal (Finset.mem_coe.mpr ha))]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra! h
      exact hab (funext h)
    have hd : ((b i : ℕ) : ℝ) - ((a i : ℕ) : ℝ) ≠ 0 := by
      intro h
      apply hi
      exact Fin.ext (by exact_mod_cast (sub_eq_zero.mp h).symm)
    refine ⟨toReal b - toReal a, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨(((z i : ℕ) : ℝ) - ((a i : ℕ) : ℝ)) / (((b i : ℕ) : ℝ) - ((a i : ℕ) : ℝ)), ?_⟩
    funext j
    have hm := hline z hz j i
    have hm' : (((z j : ℕ) : ℝ) - ((a j : ℕ) : ℝ)) * (((b i : ℕ) : ℝ) - ((a i : ℕ) : ℝ)) =
        (((z i : ℕ) : ℝ) - ((a i : ℕ) : ℝ)) * (((b j : ℕ) : ℝ) - ((a j : ℕ) : ℝ)) := by
      exact_mod_cast hm
    simp only [toReal, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linear_combination hm'

end OMA.P_a081200

open OMA.S_oeis_a081200 OMA.P_a081200 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081200.main := by
  classical
  intro n
  have he : lineCount n = (lines n).card := by
    unfold lineCount lines
    rw [← Set.ncard_coe_finset]
    congr 1
    ext s
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (collinear_iff_minor s (by omega)).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (collinear_iff_minor s (by omega)).mpr h2⟩
  rw [he]
  have h := (twice_lines n).symm.trans (words_card n)
  omega
