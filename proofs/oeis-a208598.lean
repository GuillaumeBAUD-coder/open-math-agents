import OMAStatements.S_oeis_a208598
import Mathlib

/-! Proof for OEIS A208598: Burnside's lemma for the rotation group `ℤ/4`. The identity fixes all
`N(n)` labelings, rotations by 1 and 3 fix only the zero labeling, and the half-turn fixes the
`2n + 1` labelings `(c, -c, c, -c)`, so `4 a(n) = N(n) + 2n + 3`. Counting by the partial sum
`s = v₀ + v₁` gives `N(n) = Σ_{|s| ≤ 2n} (2n + 1 - |s|)^2 = (2n + 1)(8n^2 + 8n + 3)/3`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P208598
open OMA.S_oeis_a208598

lemma mem_L {n : ℕ} {v : Fin 4 → ℤ} :
    v ∈ L n ↔ (∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ n) ∧ v 0 + v 1 + v 2 + v 3 = 0 := by
  simp [L, B, Fintype.mem_piFinset, Fin.sum_univ_four]

abbrev G := Multiplicative (Fin 4)
abbrev X (n : ℕ) := {v : Fin 4 → ℤ // v ∈ L n}

lemma rot_mem {n : ℕ} (k : Fin 4) {v : Fin 4 → ℤ} (hv : v ∈ L n) :
    (fun i => v (i + k)) ∈ L n := by
  simp only [L, Finset.mem_filter, Fintype.mem_piFinset] at hv ⊢
  refine ⟨fun i => hv.1 _, ?_⟩
  rw [← hv.2]; exact Equiv.sum_comp (Equiv.addRight k) v

instance act (n : ℕ) : MulAction G (X n) where
  smul g x := ⟨fun i => x.1 (i + Multiplicative.toAdd g), rot_mem _ x.2⟩
  one_smul x := by
    apply Subtype.ext; funext i
    show x.1 (i + Multiplicative.toAdd 1) = _
    simp
  mul_smul g h x := by
    apply Subtype.ext; funext i
    show x.1 (i + Multiplicative.toAdd (g * h)) = x.1 (i + Multiplicative.toAdd g + Multiplicative.toAdd h)
    rw [toAdd_mul, add_assoc]

lemma smul_val {n : ℕ} (g : G) (x : X n) (i : Fin 4) :
    (g • x).1 i = x.1 (i + Multiplicative.toAdd g) := rfl

open Classical in
noncomputable def cls (n : ℕ) (v : Fin 4 → ℤ) : Finset (Fin 4 → ℤ) :=
  (L n).filter (fun w => ∃ k : Fin 4, w = fun i => v (i + k))

lemma cls_rot (n : ℕ) (v : Fin 4 → ℤ) (g : Fin 4) : cls n (fun i => v (i + g)) = cls n v := by
  ext w
  simp only [cls, Finset.mem_filter]
  constructor
  · rintro ⟨hw, k, rfl⟩
    exact ⟨hw, k + g, by funext i; simp [add_assoc]⟩
  · rintro ⟨hw, k, rfl⟩
    exact ⟨hw, k - g, by funext i; simp [add_assoc]⟩

open Classical in
lemma a_eq (n : ℕ) : a n = Fintype.card (MulAction.orbitRel.Quotient G (X n)) := by
  let F : MulAction.orbitRel.Quotient G (X n) → Finset (Fin 4 → ℤ) :=
    Quotient.lift (fun x : X n => cls n x.1) (fun x y hxy => by
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hxy
      exact cls_rot n y.1 (Multiplicative.toAdd g))
  have hF : Function.Injective F := by
    intro x y hxy
    induction x using Quotient.inductionOn with | h x => ?_
    induction y using Quotient.inductionOn with | h y => ?_
    have hx : x.1 ∈ cls n x.1 := by
      simp only [cls, Finset.mem_filter]; exact ⟨x.2, 0, by funext i; simp⟩
    have hxy' : cls n x.1 = cls n y.1 := hxy
    rw [hxy'] at hx
    simp only [cls, Finset.mem_filter] at hx
    obtain ⟨-, k, hk⟩ := hx
    apply Quotient.sound
    show x ∈ MulAction.orbit G y
    exact ⟨Multiplicative.ofAdd k, Subtype.ext (by rw [hk]; rfl)⟩
  have : (L n).image (fun v => (L n).filter (fun w => ∃ k : Fin 4, w = fun i => v (i + k))) =
      Finset.univ.image F := by
    ext s
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨Quotient.mk _ ⟨v, hv⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      induction x using Quotient.inductionOn with
      | h x => exact ⟨x.1, x.2, rfl⟩
  unfold a
  rw [this, Finset.card_image_of_injective _ hF, Finset.card_univ]

/-! ## Fixed points -/

open Classical in
noncomputable def fixCount (n : ℕ) (g : G) : ℕ :=
  (Finset.univ.filter (fun x : X n => g • x = x)).card

lemma fix_iff {n : ℕ} (k : Fin 4) (x : X n) :
    (Multiplicative.ofAdd k : G) • x = x ↔ ∀ i, x.1 (i + k) = x.1 i := by
  constructor
  · intro h i; exact congrArg (fun y : X n => y.1 i) h
  · intro h; exact Subtype.ext (funext h)

lemma zero_mem (n : ℕ) : (0 : Fin 4 → ℤ) ∈ L n := by
  rw [mem_L]; simp

open Classical in
lemma fix_one_eq (n : ℕ) (k : Fin 4) (hk : k = 1 ∨ k = 3) :
    fixCount n (Multiplicative.ofAdd k) = 1 := by
  unfold fixCount
  rw [Finset.card_eq_one]
  refine ⟨⟨0, zero_mem n⟩, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, fix_iff]
  constructor
  · intro h
    have hs := (mem_L.1 x.2).2
    rcases hk with rfl | rfl
    · have h0 := h 0; have h1 := h 1; have h2 := h 2
      simp only [show (0 : Fin 4) + 1 = 1 from rfl, show (1 : Fin 4) + 1 = 2 from rfl,
        show (2 : Fin 4) + 1 = 3 from rfl] at h0 h1 h2
      apply Subtype.ext; funext i
      fin_cases i <;> simp <;> omega
    · have h0 := h 0; have h1 := h 1; have h2 := h 2
      simp only [show (0 : Fin 4) + 3 = 3 from rfl, show (1 : Fin 4) + 3 = 0 from rfl,
        show (2 : Fin 4) + 3 = 1 from rfl] at h0 h1 h2
      apply Subtype.ext; funext i
      fin_cases i <;> simp <;> omega
  · rintro rfl i; rfl

open Classical in
lemma fix_zero_eq (n : ℕ) : fixCount n (Multiplicative.ofAdd 0) = (L n).card := by
  unfold fixCount
  rw [Finset.filter_true_of_mem (fun x _ => (fix_iff 0 x).2 (fun i => by simp)),
    Finset.card_univ, Fintype.card_coe]

open Classical in
lemma fix_two_eq (n : ℕ) : fixCount n (Multiplicative.ofAdd 2) = 2 * n + 1 := by
  unfold fixCount
  have hB : (B n).card = 2 * n + 1 := by
    simp only [B, Int.card_Icc]; omega
  rw [← hB]
  apply Finset.card_nbij' (fun x => x.1 0) (fun c => if h : ![c, -c, c, -c] ∈ L n then ⟨_, h⟩ else ⟨0, zero_mem n⟩)
  · intro x _
    have := (mem_L.1 x.2).1 0
    simp only [Finset.mem_coe, B, Finset.mem_Icc]; omega
  · intro c hc
    simp only [Finset.mem_coe, B, Finset.mem_Icc] at hc
    have hm : ![c, -c, c, -c] ∈ L n := by
      rw [mem_L]; refine ⟨fun i => ?_, by simp⟩
      fin_cases i <;> simp <;> omega
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, dif_pos hm, fix_iff]
    intro i; fin_cases i <;> rfl
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, fix_iff] at hx
    have hs := (mem_L.1 x.2).2
    have h0 := hx 0; have h1 := hx 1
    simp only [show (0 : Fin 4) + 2 = 2 from rfl, show (1 : Fin 4) + 2 = 3 from rfl] at h0 h1
    have e : ![x.1 0, -x.1 0, x.1 0, -x.1 0] = x.1 := by
      funext i; fin_cases i <;> simp <;> omega
    have hm : ![x.1 0, -x.1 0, x.1 0, -x.1 0] ∈ L n := by rw [e]; exact x.2
    simp only [dif_pos hm]
    exact Subtype.ext e
  · intro c hc
    simp only [Finset.mem_coe, B, Finset.mem_Icc] at hc
    have hm : ![c, -c, c, -c] ∈ L n := by
      rw [mem_L]; refine ⟨fun i => ?_, by simp⟩
      fin_cases i <;> simp <;> omega
    simp [dif_pos hm]

/-! ## Counting labelings -/

/-- triples `(a, b, c)` whose negated sum is also in range. -/
noncomputable def Q (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (B n ×ˢ B n ×ˢ B n).filter (fun t => -(n : ℤ) ≤ t.1 + t.2.1 + t.2.2 ∧ t.1 + t.2.1 + t.2.2 ≤ n)

lemma L_eq_Q (n : ℕ) : (L n).card = (Q n).card := by
  apply Finset.card_nbij' (fun v => (v 0, v 1, v 2)) (fun t => ![t.1, t.2.1, t.2.2, -(t.1 + t.2.1 + t.2.2)])
  · intro v hv
    rw [Finset.mem_coe, mem_L] at hv
    have h0 := hv.1 0; have h1 := hv.1 1; have h2 := hv.1 2; have h3 := hv.1 3
    simp only [Finset.mem_coe, Q, Finset.mem_filter, Finset.mem_product, B, Finset.mem_Icc]
    omega
  · intro t ht
    simp only [Finset.mem_coe, Q, Finset.mem_filter, Finset.mem_product, B, Finset.mem_Icc] at ht
    rw [Finset.mem_coe, mem_L]
    refine ⟨fun i => ?_, by simp⟩
    fin_cases i <;> simp <;> omega
  · intro v hv
    rw [Finset.mem_coe, mem_L] at hv
    funext i; fin_cases i <;> simp; linarith [hv.2]
  · intro t _; simp

lemma pair_fiber (n : ℕ) (s : ℤ) (hs : |s| ≤ 2 * n) :
    (((B n ×ˢ B n).filter (fun p : ℤ × ℤ => p.1 + p.2 = s)).card : ℤ) = 2 * n + 1 - |s| := by
  have h1 : ((B n ×ˢ B n).filter (fun p : ℤ × ℤ => p.1 + p.2 = s)).card =
      ((B n).filter (fun x => -(n : ℤ) ≤ s - x ∧ s - x ≤ n)).card := by
    apply Finset.card_nbij' (fun p => p.1) (fun x => (x, s - x))
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, B, Finset.mem_Icc] at hp ⊢
      omega
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, B, Finset.mem_Icc] at hx ⊢
      omega
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, B, Finset.mem_Icc] at hp
      ext <;> simp <;> omega
    · intro x _; rfl
  rw [h1]
  rcases le_or_gt 0 s with h | h
  · have : (B n).filter (fun x => -(n : ℤ) ≤ s - x ∧ s - x ≤ n) = Finset.Icc (s - n) n := by
      ext x; simp only [B, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this, Int.card_Icc, abs_of_nonneg h]
    rw [abs_of_nonneg h] at hs
    omega
  · have : (B n).filter (fun x => -(n : ℤ) ≤ s - x ∧ s - x ≤ n) = Finset.Icc (-(n : ℤ)) (s + n) := by
      ext x; simp only [B, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this, Int.card_Icc, abs_of_neg h]
    rw [abs_of_neg h] at hs
    omega

lemma third_count (n : ℕ) (s : ℤ) (hs : |s| ≤ 2 * n) :
    (((B n).filter (fun c => -(n : ℤ) ≤ s + c ∧ s + c ≤ n)).card : ℤ) = 2 * n + 1 - |s| := by
  rcases le_or_gt 0 s with h | h
  · have : (B n).filter (fun c => -(n : ℤ) ≤ s + c ∧ s + c ≤ n) = Finset.Icc (-(n : ℤ)) (n - s) := by
      ext x; simp only [B, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this, Int.card_Icc, abs_of_nonneg h]
    rw [abs_of_nonneg h] at hs
    omega
  · have : (B n).filter (fun c => -(n : ℤ) ≤ s + c ∧ s + c ≤ n) = Finset.Icc (-(n : ℤ) - s) n := by
      ext x; simp only [B, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this, Int.card_Icc, abs_of_neg h]
    rw [abs_of_neg h] at hs
    omega

lemma sum_sq (K : ℤ) (M : ℕ) :
    3 * ∑ s ∈ Finset.Icc (-(M : ℤ)) M, (K - |s|) ^ 2 =
      3 * (2 * M + 1) * K ^ 2 - 6 * K * M * (M + 1) + M * (M + 1) * (2 * M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have e : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) M)) := by
      ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), mul_add, mul_add, ih]
    rw [abs_of_neg (by omega), abs_of_pos (by omega)]
    push_cast; ring

lemma card_L (n : ℕ) : 3 * ((L n).card : ℤ) = 16 * n ^ 3 + 24 * n ^ 2 + 14 * n + 3 := by
  rw [L_eq_Q]
  have hQ : (Q n).card = ∑ p ∈ B n ×ˢ B n,
      ((B n).filter (fun c => -(n : ℤ) ≤ (p.1 + p.2) + c ∧ (p.1 + p.2) + c ≤ n)).card := by
    have : Q n = Finset.map
        ⟨fun x => (x.1.1, x.1.2, x.2), fun x y h => by
          simp only [Prod.mk.injEq] at h
          obtain ⟨⟨a1, b1⟩, c1⟩ := x; obtain ⟨⟨a2, b2⟩, c2⟩ := y
          simp only at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl⟩
        ((B n ×ˢ B n).sigma (fun p => (B n).filter
          (fun c => -(n : ℤ) ≤ (p.1 + p.2) + c ∧ (p.1 + p.2) + c ≤ n))) := by
      ext ⟨a, b, c⟩
      simp only [Q, Finset.mem_filter, Finset.mem_product, Finset.mem_map, Finset.mem_sigma,
        Sigma.exists, Prod.exists]
      constructor
      · rintro ⟨⟨ha, hb, hc⟩, h⟩
        exact ⟨a, b, c, ⟨⟨ha, hb⟩, hc, by simpa [add_assoc] using h⟩, rfl⟩
      · rintro ⟨a', b', c', ⟨⟨ha, hb⟩, hc, h⟩, he⟩
        have he' : (a', b', c') = (a, b, c) := he
        obtain ⟨rfl, rfl, rfl⟩ : a' = a ∧ b' = b ∧ c' = c := by simpa using he'
        exact ⟨⟨ha, hb, hc⟩, by simpa [add_assoc] using h⟩
    rw [this, Finset.card_map, Finset.card_sigma]
  have hB : ∀ p ∈ B n ×ˢ B n, |p.1 + p.2| ≤ 2 * (n : ℤ) := by
    intro p hp
    simp only [Finset.mem_product, B, Finset.mem_Icc] at hp
    rw [abs_le]; constructor <;> omega
  rw [hQ]; push_cast
  rw [Finset.sum_congr rfl (fun p hp => third_count n (p.1 + p.2) (hB p hp))]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℤ × ℤ => p.1 + p.2)
    (t := Finset.Icc (-((2 * n : ℕ) : ℤ)) ((2 * n : ℕ) : ℤ)) (fun p hp => by
      have := hB p hp
      rw [abs_le] at this
      simp only [Finset.mem_Icc]; push_cast; omega)]
  have hfib : ∀ s ∈ Finset.Icc (-((2 * n : ℕ) : ℤ)) ((2 * n : ℕ) : ℤ),
      (∑ p ∈ (B n ×ˢ B n).filter (fun p : ℤ × ℤ => p.1 + p.2 = s), (2 * (n : ℤ) + 1 - |p.1 + p.2|)) =
        (2 * (n : ℤ) + 1 - |s|) ^ 2 := by
    intro s hs
    have hs' : |s| ≤ 2 * (n : ℤ) := by
      simp only [Finset.mem_Icc] at hs; push_cast at hs; rw [abs_le]; constructor <;> omega
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.sum_const, nsmul_eq_mul, pair_fiber n s hs', sq]
  rw [Finset.sum_congr rfl hfib, sum_sq]
  push_cast; ring

/-! ## Burnside -/

open Classical in
lemma burnside (n : ℕ) : Fintype.card (MulAction.orbitRel.Quotient G (X n)) * 4 =
    (L n).card + 2 * n + 3 := by
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (X n)
  have hG : Fintype.card G = 4 := by simp
  have hfix : ∀ g : G, Fintype.card (MulAction.fixedBy (X n) g) = fixCount n g := by
    intro g; classical
    unfold fixCount
    rw [← Fintype.card_subtype]; rfl
  have hsum : (∑ g : G, fixCount n g) = ∑ k : Fin 4, fixCount n (Multiplicative.ofAdd k) :=
    (Fintype.sum_equiv Multiplicative.ofAdd _ _ (fun _ => rfl)).symm
  rw [hG] at hb
  simp only [hfix] at hb
  rw [hsum, Fin.sum_univ_four, fix_zero_eq, fix_two_eq, fix_one_eq n 1 (Or.inl rfl),
    fix_one_eq n 3 (Or.inr rfl)] at hb
  change _ = Fintype.card (MulAction.orbitRel.Quotient G (X n)) * 4 at hb
  omega

open Classical in
lemma closed (n : ℕ) : 3 * (a n : ℤ) = 4 * n ^ 3 + 6 * n ^ 2 + 5 * n + 3 := by
  have hb := burnside n
  rw [← a_eq] at hb
  have hL := card_L n
  have : (a n : ℤ) * 4 = (L n).card + 2 * n + 3 := by exact_mod_cast hb
  linarith

end OMA.P208598

theorem OMA.solution : type_of% @OMA.S_oeis_a208598.main := by
  refine ⟨fun n _ => OMA.P208598.closed n, fun n hn => ?_⟩
  have h0 := OMA.P208598.closed n
  have h1 := OMA.P208598.closed (n - 1)
  have h2 := OMA.P208598.closed (n - 2)
  have h3 := OMA.P208598.closed (n - 3)
  have h4 := OMA.P208598.closed (n - 4)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, Nat.add_sub_cancel] at h0 h1 h2 h3 h4 ⊢
  push_cast at h0 h1 h2 h3 h4
  linarith
