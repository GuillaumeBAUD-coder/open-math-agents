import OMAStatements.S_oeis_a272515
import Mathlib

/-!
Proof of the asymptotic a(n) ~ 3^n / 6 for A272515.

Maps Fin n -> Fin 3 whose three fibres are nonempty and of pairwise distinct sizes (the set D)
are exactly the labelled versions of the counted partitions, six per partition: 6 a(n) <= 3^n and
|D| <= 6 a(n). A map outside D misses a value (at most 3 * 2^n maps) or has two fibres of equal
size; the latter maps are at most 3 * W(n) with W(n) = sum_s C(n,s) C(s, s/2), and by the
Cauchy-Schwarz inequality and C(s, s/2)^2 (s+1) <= 4^s one gets W(n)^2 * 2 (n+1) <= 3 * 9^n,
so W(n) / 3^n tends to 0.
-/

namespace A272515

open Finset

lemma cb_bound (j : ℕ) : Nat.centralBinom j ^ 2 * (2 * j + 1) ≤ 16 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := Nat.succ_mul_centralBinom_succ j
    have h2 : (j + 1) ^ 2 * (Nat.centralBinom (j + 1) ^ 2 * (2 * (j + 1) + 1))
        ≤ (j + 1) ^ 2 * 16 ^ (j + 1) := by
      calc (j + 1) ^ 2 * (Nat.centralBinom (j + 1) ^ 2 * (2 * (j + 1) + 1))
          = ((j + 1) * Nat.centralBinom (j + 1)) ^ 2 * (2 * j + 3) := by ring
        _ = (2 * (2 * j + 1) * Nat.centralBinom j) ^ 2 * (2 * j + 3) := by rw [h]
        _ = (Nat.centralBinom j ^ 2 * (2 * j + 1)) * (4 * (2 * j + 1) * (2 * j + 3)) := by ring
        _ ≤ 16 ^ j * (16 * (j + 1) ^ 2) := Nat.mul_le_mul ih (by nlinarith)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)

/-- the middle binomial coefficient -/
def w (s : ℕ) : ℕ := s.choose (s / 2)

lemma w_bound (s : ℕ) : w s ^ 2 * (s + 1) ≤ 4 ^ s := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' s
  · have h : w (2 * j) = Nat.centralBinom j := by
      unfold w
      rw [Nat.centralBinom_eq_two_mul_choose, Nat.mul_div_cancel_left j (by norm_num)]
    rw [h, pow_mul]
    exact cb_bound j
  · have h : 2 * w (2 * j + 1) = Nat.centralBinom (j + 1) := by
      unfold w
      have e : (2 * j + 1) / 2 = j := by omega
      rw [e, Nat.centralBinom_eq_two_mul_choose, show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
        Nat.choose_succ_succ', Nat.choose_symm_half]
      ring
    have h1 := cb_bound (j + 1)
    rw [← h] at h1
    have h3 : (4 : ℕ) ^ (2 * j + 1) * 4 = 16 ^ (j + 1) := by
      rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_succ]
      congr 1
    nlinarith [Nat.zero_le (w (2 * j + 1) ^ 2)]

/-- the weighted sum bounding the number of maps with two fibres of the same size -/
def W (n : ℕ) : ℕ := ∑ s ∈ range (n + 1), n.choose s * w s

lemma sum_choose_two_pow (n : ℕ) : ∑ s ∈ range (n + 1), (n.choose s : ℝ) * 2 ^ s = 3 ^ n := by
  have h := add_pow (2 : ℝ) 1 n
  norm_num at h
  rw [h]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma W_sq (n : ℕ) : (W n : ℝ) ^ 2 * (2 * (n + 1)) ≤ 3 * 9 ^ n := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (range (n + 1))
    (r := fun s => (n.choose s : ℝ) * w s)
    (f := fun s => (n.choose s : ℝ) * 2 ^ s / (s + 1))
    (g := fun s => (n.choose s : ℝ) * ((w s : ℝ) ^ 2 * (s + 1) / 2 ^ s))
    (fun s _ => by positivity) (fun s _ => by positivity)
    (fun s _ => le_of_eq (by field_simp))
  have hg : ∑ s ∈ range (n + 1), (n.choose s : ℝ) * ((w s : ℝ) ^ 2 * (s + 1) / 2 ^ s)
      ≤ 3 ^ n := by
    rw [← sum_choose_two_pow]
    refine Finset.sum_le_sum fun s _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have := w_bound s
    have h4 : ((w s : ℝ)) ^ 2 * (s + 1) ≤ 4 ^ s := by exact_mod_cast this
    calc ((w s : ℝ)) ^ 2 * (s + 1) ≤ 4 ^ s := h4
      _ = 2 ^ s * 2 ^ s := by rw [← mul_pow]; norm_num
  have hf : (∑ s ∈ range (n + 1), (n.choose s : ℝ) * 2 ^ s / (s + 1)) * (2 * (n + 1))
      ≤ 3 ^ (n + 1) := by
    rw [← sum_choose_two_pow (n + 1), Finset.sum_range_succ' _ (n + 1), Finset.sum_mul]
    have : ∀ s ∈ range (n + 1), (n.choose s : ℝ) * 2 ^ s / (s + 1) * (2 * (n + 1))
        = ((n + 1).choose (s + 1) : ℝ) * 2 ^ (s + 1) := by
      intro s _
      have e := Nat.add_one_mul_choose_eq n s
      have e' : ((n : ℝ) + 1) * n.choose s = (n + 1).choose (s + 1) * (s + 1) := by
        exact_mod_cast e
      field_simp
      rw [pow_succ]
      linear_combination (2 : ℝ) ^ s * 2 * e'
    rw [Finset.sum_congr rfl this]
    simp
  have hW : (W n : ℝ) = ∑ s ∈ range (n + 1), (n.choose s : ℝ) * w s := by
    unfold W; push_cast; rfl
  rw [hW]
  have hf0 : 0 ≤ ∑ s ∈ range (n + 1), (n.choose s : ℝ) * 2 ^ s / (s + 1) :=
    Finset.sum_nonneg fun s _ => by positivity
  calc (∑ s ∈ range (n + 1), (n.choose s : ℝ) * w s) ^ 2 * (2 * (n + 1))
      ≤ ((∑ s ∈ range (n + 1), (n.choose s : ℝ) * 2 ^ s / (s + 1)) * 3 ^ n) * (2 * (n + 1)) := by
        refine mul_le_mul_of_nonneg_right (hcs.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hg hf0
    _ = ((∑ s ∈ range (n + 1), (n.choose s : ℝ) * 2 ^ s / (s + 1)) * (2 * (n + 1))) * 3 ^ n := by
        ring
    _ ≤ 3 ^ (n + 1) * 3 ^ n := mul_le_mul_of_nonneg_right hf (by positivity)
    _ = 3 * 9 ^ n := by
        rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]; ring

lemma W_tendsto : Filter.Tendsto (fun n : ℕ => (W n : ℝ) / 3 ^ n) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => Real.sqrt (3 / (2 * ((n : ℝ) + 1)))) Filter.atTop
      (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 3 / (2 * ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 / 2 : ℝ)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) h1
  apply Real.le_sqrt_of_sq_le
  have := W_sq n
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have e : ((3 : ℝ) ^ n) ^ 2 = 9 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e]
  linarith


/-- fibre of a map -/
abbrev fib {n : ℕ} (f : Fin n → Fin 3) (i : Fin 3) : Finset (Fin n) :=
  univ.filter fun x => f x = i

/-- the partitions counted by the sequence -/
def G (n : ℕ) : Finset (Finpartition (Finset.univ : Finset (Fin n))) :=
  (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin n)))).filter fun P =>
    P.parts.card = 3 ∧ ∀ s ∈ P.parts, ∀ t ∈ P.parts, s ≠ t → s.card ≠ t.card

/-- maps onto Fin 3 with fibres of pairwise distinct sizes -/
def D (n : ℕ) : Finset (Fin n → Fin 3) :=
  univ.filter fun f => (∀ i, (fib f i).Nonempty) ∧ ∀ i j, i ≠ j → (fib f i).card ≠ (fib f j).card

/-- a labelling of the three blocks -/
noncomputable def lab {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (h : P.parts.card = 3) : {B // B ∈ P.parts} ≃ Fin 3 :=
  Finset.equivFinOfCardEq h

/-- the map sending a point to the label of its block -/
noncomputable def F {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (h : P.parts.card = 3) : Fin n → Fin 3 :=
  fun x => lab P h ⟨P.part x, P.part_mem.2 (mem_univ x)⟩

lemma fib_F {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (h : P.parts.card = 3) (i : Fin 3) : fib (F P h) i = ((lab P h).symm i).1 := by
  ext x
  rw [mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · intro hx
    have hx' : lab P h ⟨P.part x, P.part_mem.2 (mem_univ x)⟩ = i := hx
    rw [← hx', Equiv.symm_apply_apply]
    exact P.mem_part_self.2 (mem_univ x)
  · intro hx
    have := P.part_eq_of_mem ((lab P h).symm i).2 hx
    have e : (⟨P.part x, P.part_mem.2 (mem_univ x)⟩ : {B // B ∈ P.parts}) = (lab P h).symm i :=
      Subtype.ext this
    show lab P h ⟨P.part x, P.part_mem.2 (mem_univ x)⟩ = i
    rw [e, Equiv.apply_symm_apply]

lemma fib_comp {n : ℕ} (f : Fin n → Fin 3) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    fib (σ ∘ f) j = fib f (σ.symm j) := by
  ext x
  simp [fib, Equiv.eq_symm_apply]

lemma parts_eq {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (h : P.parts.card = 3) (σ : Equiv.Perm (Fin 3)) :
    P.parts = univ.image (fib (σ ∘ F P h)) := by
  ext B
  simp only [mem_image, mem_univ, true_and]
  constructor
  · intro hB
    refine ⟨σ (lab P h ⟨B, hB⟩), ?_⟩
    rw [fib_comp, fib_F]
    simp
  · rintro ⟨j, rfl⟩
    rw [fib_comp, fib_F]
    exact ((lab P h).symm _).2

lemma F_surj {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (h : P.parts.card = 3) (i : Fin 3) : ∃ x, F P h x = i := by
  have hne : (fib (F P h) i).Nonempty := by
    rw [fib_F]
    exact P.nonempty_of_mem_parts ((lab P h).symm i).2
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, (mem_filter.1 hx).2⟩

/-- the map from labelled good partitions to maps -/
noncomputable def Psi (n : ℕ) (p : {P // P ∈ G n} × Equiv.Perm (Fin 3)) : Fin n → Fin 3 :=
  p.2 ∘ F p.1.1 (mem_filter.1 p.1.2).2.1

lemma Psi_inj (n : ℕ) : Function.Injective (Psi n) := by
  rintro ⟨⟨P, hP⟩, σ⟩ ⟨⟨Q, hQ⟩, τ⟩ hpq
  simp only [Psi] at hpq
  have hPQ : P = Q := by
    apply Finpartition.ext
    rw [parts_eq P (mem_filter.1 hP).2.1 σ, parts_eq Q (mem_filter.1 hQ).2.1 τ, hpq]
  subst hPQ
  have hστ : σ = τ := by
    ext i
    obtain ⟨x, hx⟩ := F_surj P (mem_filter.1 hP).2.1 i
    have := congrFun hpq x
    simp only [Function.comp_apply, hx] at this
    rw [this]
  subst hστ
  rfl

lemma card_dom (n : ℕ) : Fintype.card ({P // P ∈ G n} × Equiv.Perm (Fin 3)) = (G n).card * 6 := by
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_perm, Fintype.card_fin]
  rfl

lemma upper (n : ℕ) : (G n).card * 6 ≤ 3 ^ n := by
  have := Fintype.card_le_of_injective (Psi n) (Psi_inj n)
  rw [card_dom] at this
  simpa using this

lemma fib_inj {n : ℕ} {f : Fin n → Fin 3}
    (hd : ∀ i j, i ≠ j → (fib f i).card ≠ (fib f j).card) : Function.Injective (fib f) := by
  intro i j hij
  by_contra hne
  exact hd i j hne (by rw [hij])

lemma D_sub (n : ℕ) : D n ⊆ univ.image (Psi n) := by
  intro f hf
  obtain ⟨hne, hd⟩ := (mem_filter.1 hf).2
  have hinj := fib_inj hd
  let P : Finpartition (Finset.univ : Finset (Fin n)) :=
    Finpartition.ofExistsUnique (univ.image (fib f)) (fun p _ => subset_univ p)
      (by
        intro x _
        refine ⟨fib f (f x), ⟨mem_image_of_mem _ (mem_univ _), by simp [fib]⟩, ?_⟩
        rintro t ⟨ht, hxt⟩
        obtain ⟨j, -, rfl⟩ := mem_image.1 ht
        have : f x = j := (mem_filter.1 hxt).2
        rw [this])
      (by
        intro h0
        obtain ⟨j, -, hj⟩ := mem_image.1 h0
        exact (hne j).ne_empty hj)
  have hparts : P.parts = univ.image (fib f) := rfl
  have hcard : P.parts.card = 3 := by
    rw [hparts, card_image_of_injective _ hinj]
    rfl
  have hPG : P ∈ G n := by
    refine mem_filter.2 ⟨mem_univ _, hcard, ?_⟩
    intro s hs t ht hst
    rw [hparts] at hs ht
    obtain ⟨i, -, rfl⟩ := mem_image.1 hs
    obtain ⟨j, -, rfl⟩ := mem_image.1 ht
    exact hd i j (fun h => hst (by rw [h]))
  have hmem : ∀ i, fib f i ∈ P.parts := fun i => by
    rw [hparts]; exact mem_image_of_mem _ (mem_univ _)
  let τ : Fin 3 → Fin 3 := fun i => lab P hcard ⟨fib f i, hmem i⟩
  have hτinj : Function.Injective τ := by
    intro i j hij
    have := (lab P hcard).injective hij
    exact hinj (Subtype.mk.inj this)
  have hτ : Function.Bijective τ := ⟨hτinj, Finite.injective_iff_surjective.1 hτinj⟩
  have hF : ∀ x, F P hcard x = τ (f x) := by
    intro x
    have : P.part x = fib f (f x) := P.part_eq_of_mem (hmem (f x)) (by simp [fib])
    simp only [F, τ]
    congr 1
    exact Subtype.ext this
  refine mem_image.2 ⟨(⟨P, hPG⟩, (Equiv.ofBijective τ hτ).symm), mem_univ _, ?_⟩
  funext x
  simp only [Psi, Function.comp_apply]
  rw [hF x]
  exact (Equiv.ofBijective τ hτ).symm_apply_apply (f x)

lemma lower1 (n : ℕ) : (D n).card ≤ (G n).card * 6 := by
  calc (D n).card ≤ (univ.image (Psi n)).card := card_le_card (D_sub n)
    _ ≤ (univ : Finset ({P // P ∈ G n} × Equiv.Perm (Fin 3))).card := card_image_le
    _ = (G n).card * 6 := by rw [card_univ, card_dom]

/-- maps missing the value i -/
def Z (n : ℕ) (i : Fin 3) : Finset (Fin n → Fin 3) := univ.filter fun f => fib f i = ∅

/-- maps with two fibres of the same size -/
def E (n : ℕ) (i j : Fin 3) : Finset (Fin n → Fin 3) :=
  univ.filter fun f => (fib f i).card = (fib f j).card

lemma card_Z (n : ℕ) (i : Fin 3) : (Z n i).card ≤ 2 ^ n := by
  have hsub : Z n i ⊆ Fintype.piFinset (fun _ : Fin n => (univ : Finset (Fin 3)).erase i) := by
    intro f hf
    have h0 : fib f i = ∅ := (mem_filter.1 hf).2
    rw [Fintype.mem_piFinset]
    intro x
    refine mem_erase.2 ⟨fun hx => ?_, mem_univ _⟩
    have : x ∈ fib f i := mem_filter.2 ⟨mem_univ _, hx⟩
    rw [h0] at this
    exact absurd this (notMem_empty x)
  refine (card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  simp

lemma fin3_aux : ∀ i j a b : Fin 3, i ≠ j → (a = i ↔ b = i) →
    ((a = i ∨ a = j) ↔ (b = i ∨ b = j)) → a = b := by decide

lemma card_E (n : ℕ) (i j : Fin 3) (hij : i ≠ j) : (E n i j).card ≤ W n := by
  have key : (E n i j).card ≤
      ((univ : Finset (Fin n)).powerset.sigma fun U => powersetCard (U.card / 2) U).card := by
    apply Finset.card_le_card_of_injOn (fun f => ⟨fib f i ∪ fib f j, fib f i⟩)
    · intro f hf
      have hc : (fib f i).card = (fib f j).card := (mem_filter.1 hf).2
      have hdis : Disjoint (fib f i) (fib f j) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        exact hij ((mem_filter.1 hx).2.symm.trans (mem_filter.1 hx').2)
      refine mem_sigma.2 ⟨mem_powerset.2 (subset_univ _), mem_powersetCard.2 ⟨subset_union_left, ?_⟩⟩
      show (fib f i).card = (fib f i ∪ fib f j).card / 2
      rw [card_union_of_disjoint hdis, ← hc]
      omega
    · intro f _ g _ hfg
      simp only [Sigma.mk.injEq] at hfg
      obtain ⟨hU, hA⟩ := hfg
      have hA' : fib f i = fib g i := eq_of_heq hA
      funext x
      refine fin3_aux i j (f x) (g x) hij ?_ ?_
      · have := Finset.ext_iff.1 hA' x
        simpa [fib] using this
      · have := Finset.ext_iff.1 hU x
        simpa [fib] using this
  refine key.trans (le_of_eq ?_)
  rw [card_sigma]
  simp only [card_powersetCard]
  rw [Finset.sum_powerset_apply_card (fun m => m.choose (m / 2))]
  simp only [card_univ, Fintype.card_fin, smul_eq_mul]
  rfl

lemma cover (n : ℕ) : (univ : Finset (Fin n → Fin 3)) ⊆
    D n ∪ Z n 0 ∪ Z n 1 ∪ Z n 2 ∪ E n 0 1 ∪ E n 0 2 ∪ E n 1 2 := by
  intro f _
  by_cases hf : f ∈ D n
  · simp [hf]
  · have hf' : ¬ ((∀ i, (fib f i).Nonempty) ∧
        ∀ i j, i ≠ j → (fib f i).card ≠ (fib f j).card) := fun h => hf (mem_filter.2 ⟨mem_univ _, h⟩)
    rw [not_and_or] at hf'
    simp only [mem_union, Z, E, mem_filter, mem_univ, true_and]
    rcases hf' with h | h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      fin_cases i <;> simp_all
    · push Not at h
      obtain ⟨i, j, hij, hc⟩ := h
      have hc' := hc.symm
      fin_cases i <;> fin_cases j <;> simp_all

lemma lower (n : ℕ) : 3 ^ n ≤ (G n).card * 6 + 3 * 2 ^ n + 3 * W n := by
  have h := card_le_card (cover n)
  have h1 : (univ : Finset (Fin n → Fin 3)).card = 3 ^ n := by simp
  rw [h1] at h
  have hu := fun (s t : Finset (Fin n → Fin 3)) => card_union_le s t
  have := lower1 n
  have := card_Z n 0
  have := card_Z n 1
  have := card_Z n 2
  have := card_E n 0 1 (by decide)
  have := card_E n 0 2 (by decide)
  have := card_E n 1 2 (by decide)
  have := hu (D n ∪ Z n 0 ∪ Z n 1 ∪ Z n 2 ∪ E n 0 1 ∪ E n 0 2) (E n 1 2)
  have := hu (D n ∪ Z n 0 ∪ Z n 1 ∪ Z n 2 ∪ E n 0 1) (E n 0 2)
  have := hu (D n ∪ Z n 0 ∪ Z n 1 ∪ Z n 2) (E n 0 1)
  have := hu (D n ∪ Z n 0 ∪ Z n 1) (Z n 2)
  have := hu (D n ∪ Z n 0) (Z n 1)
  have := hu (D n) (Z n 0)
  omega

lemma final : Filter.Tendsto (fun n : ℕ => ((G n).card : ℝ) / ((3 : ℝ) ^ n / 6)) Filter.atTop
    (nhds 1) := by
  have hlow : Filter.Tendsto (fun n : ℕ => 1 - 3 * (2 / 3 : ℝ) ^ n - 3 * ((W n : ℝ) / 3 ^ n))
      Filter.atTop (nhds 1) := by
    have h2 : Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (h2.const_mul 3)).sub (W_tendsto.const_mul 3)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · have h := lower n
    have h' : (3 : ℝ) ^ n ≤ (G n).card * 6 + 3 * 2 ^ n + 3 * W n := by exact_mod_cast h
    have h3 : (0 : ℝ) < 3 ^ n := by positivity
    show 1 - 3 * (2 / 3 : ℝ) ^ n - 3 * ((W n : ℝ) / 3 ^ n) ≤ ((G n).card : ℝ) / ((3 : ℝ) ^ n / 6)
    rw [div_pow, div_div_eq_mul_div, le_div_iff₀ h3]
    have e : (1 - 3 * ((2 : ℝ) ^ n / 3 ^ n) - 3 * ((W n : ℝ) / 3 ^ n)) * 3 ^ n
        = 3 ^ n - 3 * 2 ^ n - 3 * W n := by
      field_simp
    rw [e]
    linarith
  · have h := upper n
    have h' : ((G n).card : ℝ) * 6 ≤ 3 ^ n := by exact_mod_cast h
    have h3 : (0 : ℝ) < 3 ^ n := by positivity
    show ((G n).card : ℝ) / ((3 : ℝ) ^ n / 6) ≤ 1
    rw [div_div_eq_mul_div, div_le_one h3]
    exact h'

end A272515

theorem OMA.solution : type_of% @OMA.S_oeis_a272515.main := A272515.final
