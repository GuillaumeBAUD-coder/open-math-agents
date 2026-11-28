import OMAStatements.S_mo_448509
import Mathlib

namespace OMA.P448509
open OMA.S_mo_448509 Finset

lemma uniq {ι : Type*} [Fintype ι] (M : Mat ι) (v : ℕ) (h : freq M v = 1) (x y : ι × ι)
    (hx : entry M x = v) (hy : entry M y = v) : x = y := by
  have h' : (univ.filter (fun p => entry M p = v)).card ≤ 1 := by
    unfold freq at h; omega
  exact Finset.card_le_one.mp h' x (by simp [hx]) y (by simp [hy])

lemma exists_of {ι : Type*} [Fintype ι] (M : Mat ι) (v : ℕ) (h : freq M v = 1) :
    ∃ x : ι × ι, entry M x = v := by
  have h' : 0 < (univ.filter (fun p => entry M p = v)).card := by unfold freq at h; omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h'
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩

lemma not_free {ι : Type*} [Fintype ι] (A : Mat ι) (i j : ι) (h : freq A (A i j) = 1) :
    i ∉ free A ∧ j ∉ free A := by
  constructor
  · intro hi
    simp only [free, mem_filter, mem_univ, true_and] at hi
    exact (hi j).1 h
  · intro hj
    simp only [free, mem_filter, mem_univ, true_and] at hj
    exact (hj i).2 h

lemma of_not_free {ι : Type*} [Fintype ι] (A : Mat ι) (i : ι) (hi : i ∉ free A) :
    ∃ j, freq A (A i j) = 1 ∨ freq A (A j i) = 1 := by
  by_contra hc
  push Not at hc
  apply hi
  simp only [free, mem_filter, mem_univ, true_and]
  exact hc

lemma mem_cand {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Mat ι) (p : Equiv.Perm ι) :
    p ∈ cand A B ↔ ∀ i j, freq A (A i j) = 1 → B (p i) (p j) = A i j := by
  unfold cand
  simp

lemma freq_perm {ι : Type*} [Fintype ι] (A B : Mat ι) (p : Equiv.Perm ι)
    (h : ∀ i j, B (p i) (p j) = A i j) (v : ℕ) : freq A v = freq B v := by
  unfold freq
  apply Finset.card_nbij' (fun x => (p x.1, p x.2)) (fun y => (p.symm y.1, p.symm y.2))
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    simp only [entry] at hx ⊢
    rw [h]; exact hx
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    simp only [entry] at hy ⊢
    rw [← h]; simpa using hy
  · intro x _; simp
  · intro y _; simp

lemma part1 {ι : Type*} [Fintype ι] (A : Mat ι) :
    (Fintype.card ι)^2-(Fintype.card ι-(free A).card)^2 ≤
      2*((Fintype.card ι)^2-(labels A).card) := by
  classical
  have hTS : (univ.filter (fun p : ι × ι => freq A (entry A p) = 1)).card +
      (univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1)).card = (Fintype.card ι)^2 := by
    rw [Finset.card_filter_add_card_filter_not]; simp [sq]
  have hSI : 2 * ((univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1)).image (entry A)).card
      ≤ (univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1)).card := by
    rw [Finset.card_eq_sum_card_image (entry A)
      (univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1))]
    have := Finset.card_nsmul_le_sum
      ((univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1)).image (entry A))
      (fun a => ((univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1)).filter
        fun x => entry A x = a).card) 2 ?_
    · simp only [smul_eq_mul] at this
      rw [mul_comm]; exact this
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    have hx' : freq A (entry A x) ≠ 1 := (Finset.mem_filter.mp hx).2
    have heq : ((univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1)).filter
        fun y => entry A y = entry A x) = univ.filter (fun y => entry A y = entry A x) := by
      ext y
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [h]; exact hx', h⟩
    rw [heq]
    have h1 : x ∈ univ.filter (fun y => entry A y = entry A x) := by simp
    have : 0 < freq A (entry A x) := Finset.card_pos.mpr ⟨x, h1⟩
    unfold freq at hx' this
    omega
  have hL : (labels A).card ≤ (univ.filter (fun p : ι × ι => freq A (entry A p) = 1)).card +
      ((univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1)).image (entry A)).card := by
    have : labels A ⊆ (univ.filter (fun p : ι × ι => freq A (entry A p) = 1)).image (entry A) ∪
        (univ.filter (fun p : ι × ι => ¬ freq A (entry A p) = 1)).image (entry A) := by
      intro v hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
      by_cases h : freq A (entry A x) = 1
      · exact mem_union_left _ (mem_image_of_mem _ (by simp [h]))
      · exact mem_union_right _ (mem_image_of_mem _ (by simp [h]))
    calc _ ≤ _ := card_le_card this
      _ ≤ _ := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right card_image_le _
  have hTc : (univ.filter (fun p : ι × ι => freq A (entry A p) = 1)).card ≤
      (Fintype.card ι - (free A).card)^2 := by
    have : (univ.filter (fun p : ι × ι => freq A (entry A p) = 1)) ⊆ (free A)ᶜ ×ˢ (free A)ᶜ := by
      intro x hx
      have h := (mem_filter.mp hx).2
      obtain ⟨i, j⟩ := x
      have := not_free A i j h
      simp only [mem_product, mem_compl]
      exact this
    calc _ ≤ _ := card_le_card this
      _ = _ := by rw [card_product, card_compl, sq]
  omega

lemma part2 {ι : Type*} [Fintype ι] (A : Mat ι) (hN : 0 < Fintype.card ι) :
    (free A).card ≤ 2*((Fintype.card ι)^2-(labels A).card)/(Fintype.card ι) := by
  have h1 := part1 A
  have hF : (free A).card ≤ Fintype.card ι := card_le_univ _
  rw [Nat.le_div_iff_mul_le hN]
  generalize Fintype.card ι = N at *
  generalize (free A).card = F at *
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hF
  have e1 : (F + k)^2 = k^2 + F*(F+2*k) := by ring
  have e2 : F * (F + k) ≤ F * (F + 2*k) := Nat.mul_le_mul_left _ (by omega)
  have e3 : F + k - F = k := by omega
  rw [e3] at h1
  omega

lemma part3 {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Mat ι) :
    similar A B ↔ (∀ v, freq A v = freq B v) ∧ ∃ p ∈ cand A B, ∀ i j, B (p i) (p j) = A i j := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨freq_perm A B p hp, p, (mem_cand A B p).mpr (fun i j _ => hp i j), hp⟩
  · rintro ⟨-, p, -, hp⟩
    exact ⟨p, hp⟩

lemma forced_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Mat ι}
    (hf : ∀ v, freq A v = freq B v) {p : Equiv.Perm ι} (hp : p ∈ cand A B) {i t : ι}
    (h : forced A B i t) : p i = t := by
  have hp' := (mem_cand A B p).mp hp
  rcases h with ⟨j, u, h1, h2⟩ | ⟨j, u, h1, h2⟩
  · have := uniq B (A i j) (by rw [← hf]; exact h1) (p i, p j) (t, u) (hp' i j h1) h2
    exact congrArg Prod.fst this
  · have := uniq B (A j i) (by rw [← hf]; exact h1) (p j, p i) (u, t) (hp' j i h1) h2
    exact congrArg Prod.snd this

lemma part4a {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Mat ι}
    (hf : ∀ v, freq A v = freq B v) : (cand A B).Nonempty ↔ consistent A B := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨fun i t u h1 h2 => ?_, fun i j t h1 h2 => ?_⟩
    · rw [← forced_eq hf hp h1, ← forced_eq hf hp h2]
    · apply p.injective
      rw [forced_eq hf hp h1, forced_eq hf hp h2]
  · rintro ⟨hfun, hinj⟩
    classical
    let D : ι → Prop := fun i => ∃ t, forced A B i t
    let f : {i // D i} → ι := fun i => i.2.choose
    have hfi : ∀ i, forced A B i.1 (f i) := fun i => i.2.choose_spec
    have finj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact hinj a.1 b.1 (f a) (hfi a) (hab ▸ hfi b)
    let e := Equiv.ofInjective f finj
    let p : Equiv.Perm ι := e.extendSubtype
    have hpi : ∀ i t, forced A B i t → p i = t := by
      intro i t h
      have hD : D i := ⟨t, h⟩
      have : p i = f ⟨i, hD⟩ := by
        simp only [p]
        rw [Equiv.extendSubtype_apply_of_mem e i hD]
        rfl
      rw [this]
      exact hfun i _ _ (hfi ⟨i, hD⟩) h
    refine ⟨p, (mem_cand A B p).mpr ?_⟩
    intro i j hij
    obtain ⟨⟨t, u⟩, htu⟩ := exists_of B (A i j) (by rw [← hf]; exact hij)
    have h1 : forced A B i t := Or.inl ⟨j, u, hij, htu⟩
    have h2 : forced A B j u := Or.inr ⟨i, t, hij, htu⟩
    rw [hpi i t h1, hpi j u h2]
    exact htu

lemma part4b {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Mat ι}
    (hf : ∀ v, freq A v = freq B v) {p : Equiv.Perm ι} (hp : p ∈ cand A B) :
    ∀ q : Equiv.Perm ι, q ∈ cand A B ↔ ∀ i ∉ free A, q i = p i := by
  have hp' := (mem_cand A B p).mp hp
  intro q
  constructor
  · intro hq i hi
    obtain ⟨j, hj | hj⟩ := of_not_free A i hi
    · exact forced_eq hf hq (Or.inl ⟨j, p j, hj, hp' i j hj⟩)
    · exact forced_eq hf hq (Or.inr ⟨j, p j, hj, hp' j i hj⟩)
  · intro hq
    rw [mem_cand]
    intro i j hij
    obtain ⟨hi, hj⟩ := not_free A i j hij
    rw [hq i hi, hq j hj]
    exact hp' i j hij

lemma part4c {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Mat ι}
    (hf : ∀ v, freq A v = freq B v) {p : Equiv.Perm ι} (hp : p ∈ cand A B) :
    (cand A B).card = (free A).card.factorial := by
  classical
  have h : cand A B = univ.filter (fun q : Equiv.Perm ι => ∀ i ∉ free A, q i = p i) := by
    ext q
    simp only [mem_filter, mem_univ, true_and]
    exact part4b hf hp q
  rw [h, ← Fintype.card_subtype]
  let e1 : {q : Equiv.Perm ι // ∀ i ∉ free A, q i = p i} ≃
      {g : Equiv.Perm ι // ∀ a, ¬ (a ∈ free A) → g a = a} :=
    Equiv.subtypeEquiv (Equiv.mulLeft p⁻¹) (by
      intro q
      refine forall_congr' fun a => imp_congr_right fun _ => ?_
      show q a = p a ↔ p⁻¹ (q a) = a
      rw [Equiv.Perm.inv_eq_iff_eq])
  rw [Fintype.card_congr (e1.trans (Equiv.Perm.subtypeEquivSubtypePerm (· ∈ free A)).symm),
    Fintype.card_perm]
  simp

lemma part5a {n m : ℕ} (A B : Mat (Fin n)) (hB : ∀ i j, B i j ≤ 1) :
    similar (padded A m) (padded B m) → similar A B := by
  rintro ⟨P, hP⟩
  have hr : ∀ x, P (.inr x) = .inr x := by
    intro x
    have h := hP (.inr x) (.inr x)
    rcases hc : P (.inr x) with a | b
    · rw [hc] at h
      have h' : B a a = 3 + (finProdFinEquiv (x, x)).val := h
      have := hB a a
      omega
    · rw [hc] at h
      have h' : 3 + (finProdFinEquiv (b, b)).val = 3 + (finProdFinEquiv (x, x)).val := h
      have h3 : finProdFinEquiv (b, b) = finProdFinEquiv (x, x) := Fin.ext (by omega)
      have := congrArg Prod.fst (finProdFinEquiv.injective h3)
      simp only at this
      rw [this]
  have hl : ∀ a, ∃ b, P (.inl a) = .inl b := by
    intro a
    rcases hc : P (.inl a) with b | x
    · exact ⟨b, rfl⟩
    · exfalso
      have := P.injective (hc.trans (hr x).symm)
      simp at this
  choose f hf using hl
  have finj : Function.Injective f := by
    intro a b h
    have := hf a
    rw [h, ← hf b] at this
    exact Sum.inl_injective (P.injective this)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj), fun i j => ?_⟩
  simp only [Equiv.ofBijective_apply]
  have := hP (.inl i) (.inl j)
  rw [hf i, hf j] at this
  exact this

lemma part5a' {n m : ℕ} (A B : Mat (Fin n)) :
    similar A B → similar (padded A m) (padded B m) := by
  rintro ⟨p, hp⟩
  refine ⟨Equiv.sumCongr p (Equiv.refl _), ?_⟩
  rintro (i | i) (j | j)
  · exact hp i j
  all_goals rfl

lemma part5b {n : ℕ} (A : Mat (Fin n)) (m : ℕ) : m^2 ≤ (labels (padded A m)).card := by
  have : (range (m^2)).card ≤ (labels (padded A m)).card := by
    apply card_le_card_of_injOn (fun k => 3 + k)
    · intro k hk
      simp only [coe_range, Set.mem_Iio] at hk
      rw [sq] at hk
      simp only [labels, coe_image, coe_univ, Set.image_univ, Set.mem_range]
      refine ⟨(.inr (finProdFinEquiv.symm ⟨k, hk⟩).1, .inr (finProdFinEquiv.symm ⟨k, hk⟩).2), ?_⟩
      show 3 + (finProdFinEquiv ((finProdFinEquiv.symm ⟨k, hk⟩).1,
        (finProdFinEquiv.symm ⟨k, hk⟩).2)).val = 3 + k
      simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    · intro a _ b _ h
      simpa using h
  simpa using this

lemma part5c {n : ℕ} (A : Mat (Fin n)) (h : ℕ) :
    ((n+n^h)^2-(labels (padded A (n^h))).card)^h ≤ 2^h*(n+n^h)^(h+1) := by
  have hL := part5b A (n^h)
  generalize (labels (padded A (n^h))).card = L at *
  have h1 : (n+n^h)^2 - L ≤ 2*n*(n+n^h) := by
    rw [Nat.sub_le_iff_le_add]
    nlinarith
  calc ((n+n^h)^2 - L)^h ≤ (2*n*(n+n^h))^h := Nat.pow_le_pow_left h1 h
    _ = 2^h * (n^h * (n+n^h)^h) := by rw [mul_pow, mul_pow]; ring
    _ ≤ 2^h * ((n+n^h) * (n+n^h)^h) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    _ = 2^h*(n+n^h)^(h+1) := by ring

end OMA.P448509

theorem OMA.solution : type_of% @OMA.S_mo_448509.main := by
  refine ⟨fun ι _ _ A B => ⟨OMA.P448509.part1 A, OMA.P448509.part2 A, OMA.P448509.part3 A B,
    fun hf => ⟨OMA.P448509.part4a hf, fun p hp =>
      ⟨OMA.P448509.part4c hf hp, OMA.P448509.part4b hf hp⟩⟩⟩,
    fun n m A B _ hB => ⟨⟨OMA.P448509.part5a A B hB, OMA.P448509.part5a' A B⟩,
      OMA.P448509.part5b A m, fun h => OMA.P448509.part5c A h⟩⟩
