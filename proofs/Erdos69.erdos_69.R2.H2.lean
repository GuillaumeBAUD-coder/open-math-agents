import OMAReductions.R_Erdos69_erdos_69_R2

/-! Moments of the finite CRT model. Write W as a sum over primes of
X p i, the weight of the unique residue of J hit by p at i. Then every
product of powers of X over distinct primes has its average fixed by the
Chinese remainder theorem, up to an error of one per residue choice. The
first and odd mixed moments vanish because the weights sum to zero; the
second moment is the diagonal, and the fourth is at most the diagonal plus
three pairings. -/

namespace OMA.Erdos69Moments
open Finset

lemma count_modEq (M m x : ℕ) (hm : 0 < m) :
    |(((range M).filter (fun i => i ≡ x [MOD m])).card : ℝ) - (M : ℝ) / m| ≤ 1 := by
  have h := Nat.count_modEq_card M hm x
  rw [Nat.count_eq_card_filter_range] at h
  rw [h]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ((M / m : ℕ) : ℝ) * m ≤ M := by exact_mod_cast Nat.div_mul_le_self M m
  have h2 : (M : ℝ) < ((M / m : ℕ) + 1 : ℝ) * m := by
    have := Nat.lt_div_mul_add (a := M) hm
    exact_mod_cast (by nlinarith [this] : M < (M / m + 1) * m)
  have e1 : ((M / m : ℕ) : ℝ) ≤ (M : ℝ) / m := by rw [le_div_iff₀ hm']; exact h1
  have e2 : (M : ℝ) / m < ((M / m : ℕ) : ℝ) + 1 := by rw [div_lt_iff₀ hm']; exact h2
  rw [abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

lemma solve_prime (p D c : ℕ) (hp : p.Prime) (hD : p.Coprime D) :
    ∃ y, ∀ i, p ∣ D * i + c ↔ i ≡ y [MOD p] := by
  haveI := Fact.mk hp
  have hD0 : (D : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hD h)
  refine ⟨((-(c : ZMod p)) / (D : ZMod p)).val, fun i => ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val,
    ZMod.cast_id]
  push_cast
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

lemma crt (m p x y : ℕ) (h : m.Coprime p) :
    ∃ z, ∀ i, (i ≡ x [MOD m] ∧ i ≡ y [MOD p]) ↔ i ≡ z [MOD m * p] := by
  let z := Nat.chineseRemainder h x y
  refine ⟨z, fun i => ?_⟩
  rw [← Nat.modEq_and_modEq_iff_modEq_mul h]
  have h1 := z.2.1
  have h2 := z.2.2
  constructor
  · rintro ⟨a, b⟩; exact ⟨a.trans h1.symm, b.trans h2.symm⟩
  · rintro ⟨a, b⟩; exact ⟨a.trans h1, b.trans h2⟩

section Model

variable (P J : Finset ℕ) (D b : ℕ) (w : ℕ → ℝ)

/-- The contribution of the prime `p` at position `i`. -/
noncomputable def X (p i : ℕ) : ℝ := ∑ r ∈ J, w r * if p ∣ D * i + b + r then 1 else 0

variable {P J D b w}

lemma unique_hit {p i r r' : ℕ} (hinj : Set.InjOn (fun r : ℕ => r % p) (J : Set ℕ))
    (hr : r ∈ J) (hr' : r' ∈ J) (h : p ∣ D * i + b + r) (h' : p ∣ D * i + b + r') : r = r' := by
  apply hinj hr hr'
  have e1 : D * i + b + r ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
  have e2 : D * i + b + r' ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h'
  exact Nat.ModEq.add_left_cancel' (D * i + b) (e1.trans e2.symm)

lemma X_pow {p i k : ℕ} (hk : 1 ≤ k) (hinj : Set.InjOn (fun r : ℕ => r % p) (J : Set ℕ)) :
    X J D b w p i ^ k = ∑ r ∈ J, w r ^ k * if p ∣ D * i + b + r then 1 else 0 := by
  unfold X
  by_cases h : ∃ r ∈ J, p ∣ D * i + b + r
  · obtain ⟨r0, hr0, h0⟩ := h
    have key : ∀ r ∈ J, r ≠ r0 → ¬ p ∣ D * i + b + r := fun r hr hne hd =>
      hne (unique_hit hinj hr hr0 hd h0)
    rw [Finset.sum_eq_single r0 (fun r hr hne => by simp [key r hr hne]) (fun h => absurd hr0 h),
      Finset.sum_eq_single r0 (fun r hr hne => by simp [key r hr hne]) (fun h => absurd hr0 h)]
    simp [h0]
  · push_neg at h
    have z1 : ∀ r ∈ J, (w r * if p ∣ D * i + b + r then (1 : ℝ) else 0) = 0 := fun r hr => by
      simp [h r hr]
    have z2 : ∀ r ∈ J, (w r ^ k * if p ∣ D * i + b + r then (1 : ℝ) else 0) = 0 := fun r hr => by
      simp [h r hr]
    rw [Finset.sum_eq_zero z1, Finset.sum_eq_zero z2]
    exact zero_pow (by omega)

variable (hP : ∀ p ∈ P, Nat.Prime p ∧ p.Coprime D ∧ Set.InjOn (fun r : ℕ => r % p) (J : Set ℕ))
include hP

lemma gen (M : ℕ) (Q : Finset ℕ) (hQ : Q ⊆ P) (e : ℕ → ℕ) (he : ∀ q ∈ Q, 1 ≤ e q) :
    ∀ m x : ℕ, 0 < m → (∀ q ∈ Q, m.Coprime q) →
    |∑ i ∈ (range M).filter (fun i => i ≡ x [MOD m]), ∏ q ∈ Q, X J D b w q i ^ e q
      - (M : ℝ) / m * ∏ q ∈ Q, (∑ r ∈ J, w r ^ e q) / q| ≤ ∏ q ∈ Q, ∑ r ∈ J, |w r| ^ e q := by
  induction Q using Finset.induction_on with
  | empty =>
    intro m x hm _
    simp only [Finset.prod_empty, mul_one, Finset.sum_const, nsmul_eq_mul]
    exact count_modEq M m x hm
  | insert p Q hpQ ih =>
    intro m x hm hcop
    have hpP : p ∈ P := hQ (Finset.mem_insert_self _ _)
    obtain ⟨hp, hpD, hinj⟩ := hP p hpP
    have hmp : m.Coprime p := hcop p (Finset.mem_insert_self _ _)
    have hz : ∀ r, ∃ z, ∀ i, (i ≡ x [MOD m] ∧ p ∣ D * i + b + r) ↔ i ≡ z [MOD m * p] := by
      intro r
      obtain ⟨y, hy⟩ := solve_prime p D (b + r) hp hpD
      obtain ⟨z, hz⟩ := crt m p x y hmp
      exact ⟨z, fun i => by rw [← hz i, add_assoc, hy i]⟩
    choose z hz using hz
    have ihr : ∀ r, |∑ i ∈ (range M).filter (fun i => i ≡ z r [MOD m * p]),
        ∏ q ∈ Q, X J D b w q i ^ e q
        - (M : ℝ) / (m * p : ℕ) * ∏ q ∈ Q, (∑ r ∈ J, w r ^ e q) / q| ≤
        ∏ q ∈ Q, ∑ r ∈ J, |w r| ^ e q := by
      intro r
      refine ih (fun q hq => hQ (Finset.mem_insert_of_mem hq))
        (fun q hq => he q (Finset.mem_insert_of_mem hq)) (m * p) (z r)
        (Nat.mul_pos hm hp.pos) (fun q hqQ => ?_)
      refine Nat.Coprime.mul (hcop q (Finset.mem_insert_of_mem hqQ)) ?_
      have hq := (hP q (hQ (Finset.mem_insert_of_mem hqQ))).1
      exact (Nat.coprime_primes hp hq).mpr (fun h => hpQ (h ▸ hqQ))
    -- rewrite the sum
    have hsum : ∑ i ∈ (range M).filter (fun i => i ≡ x [MOD m]),
        ∏ q ∈ insert p Q, X J D b w q i ^ e q =
        ∑ r ∈ J, w r ^ e p * ∑ i ∈ (range M).filter (fun i => i ≡ z r [MOD m * p]),
          ∏ q ∈ Q, X J D b w q i ^ e q := by
      simp_rw [Finset.prod_insert hpQ]
      rw [Finset.sum_congr rfl (fun i _ => by
        rw [X_pow (he p (Finset.mem_insert_self _ _)) hinj, Finset.sum_mul])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_filter_of_ne (p := fun i => p ∣ D * i + b + r)
        (fun i _ h => by by_contra hc; simp [hc] at h)]
      rw [Finset.filter_filter]
      rw [Finset.filter_congr (fun i _ => hz r i)]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have : p ∣ D * i + b + r := ((hz r i).mpr (Finset.mem_filter.mp hi).2).2
      simp [this]
    rw [hsum, Finset.prod_insert hpQ, Finset.prod_insert hpQ]
    have hmain : (M : ℝ) / m * ((∑ r ∈ J, w r ^ e p) / p * ∏ q ∈ Q, (∑ r ∈ J, w r ^ e q) / q) =
        ∑ r ∈ J, w r ^ e p * ((M : ℝ) / (m * p : ℕ) * ∏ q ∈ Q, (∑ r ∈ J, w r ^ e q) / q) := by
      rw [← Finset.sum_mul]
      push_cast
      have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
    rw [hmain, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
    rw [← mul_sub, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (ihr r) (by positivity)

lemma gen1 (M : ℕ) (Q : Finset ℕ) (hQ : Q ⊆ P) (e : ℕ → ℕ) (he : ∀ q ∈ Q, 1 ≤ e q) :
    |∑ i ∈ range M, ∏ q ∈ Q, X J D b w q i ^ e q
      - (M : ℝ) * ∏ q ∈ Q, (∑ r ∈ J, w r ^ e q) / q| ≤ ∏ q ∈ Q, ∑ r ∈ J, |w r| ^ e q := by
  have h := gen (b := b) (w := w) hP M Q hQ e he 1 0 one_pos (fun q _ => Nat.coprime_one_left q)
  have hf : (range M).filter (fun i => i ≡ 0 [MOD 1]) = range M :=
    Finset.filter_true_of_mem (fun i _ => Nat.modEq_one)
  rw [hf] at h
  simpa using h

lemma pow_sum_le (k : ℕ) (hk : 1 ≤ k) :
    ∑ r ∈ J, |w r| ^ k ≤ (∑ r ∈ J, |w r|) ^ k := by
  have hs : 0 ≤ ∑ r ∈ J, |w r| := Finset.sum_nonneg (fun r _ => abs_nonneg _)
  calc ∑ r ∈ J, |w r| ^ k = ∑ r ∈ J, |w r| * |w r| ^ (k - 1) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [← pow_succ', Nat.sub_add_cancel hk]
    _ ≤ ∑ r ∈ J, |w r| * (∑ r ∈ J, |w r|) ^ (k - 1) := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ?_ _) (abs_nonneg _)
        exact Finset.single_le_sum (f := fun r => |w r|) (fun r _ => abs_nonneg _) hr
    _ = (∑ r ∈ J, |w r|) ^ k := by
        rw [← Finset.sum_mul, ← pow_succ', Nat.sub_add_cancel hk]

/-- Main term of a tuple of primes. -/
noncomputable def mu {n : ℕ} (t : Fin n → ℕ) : ℝ :=
  ∏ q ∈ univ.image t, (∑ r ∈ J, w r ^ #{j | t j = q}) / q

omit hP in
lemma mu_def {n : ℕ} (t : Fin n → ℕ) : mu (J := J) (w := w) t =
  ∏ q ∈ univ.image t, (∑ r ∈ J, w r ^ #{j | t j = q}) / q := rfl

lemma tuple (M n : ℕ) (t : Fin n → ℕ) (ht : ∀ j, t j ∈ P) :
    |∑ i ∈ range M, ∏ j, X J D b w (t j) i - (M : ℝ) * mu (J := J) (w := w) t| ≤
      (∑ r ∈ J, |w r|) ^ n := by
  have hQ : univ.image t ⊆ P := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact ht j
  have he : ∀ q ∈ univ.image t, 1 ≤ #{j | t j = q} := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.card_pos.mpr ⟨j, by simp⟩
  have h := gen1 (b := b) (w := w) hP M (univ.image t) hQ (fun q => #{j | t j = q}) he
  have hprod : ∀ i, ∏ j, X J D b w (t j) i =
      ∏ q ∈ univ.image t, X J D b w q i ^ #{j | t j = q} := fun i =>
    Finset.prod_comp (fun q => X J D b w q i) t
  simp_rw [hprod]
  refine h.trans ?_
  calc ∏ q ∈ univ.image t, ∑ r ∈ J, |w r| ^ #{j | t j = q}
      ≤ ∏ q ∈ univ.image t, (∑ r ∈ J, |w r|) ^ #{j | t j = q} :=
        Finset.prod_le_prod (fun q _ => Finset.sum_nonneg (fun r _ => by positivity))
          (fun q hq => pow_sum_le (w := w) hP _ (he q hq))
    _ = (∑ r ∈ J, |w r|) ^ n := by
        rw [Finset.prod_pow_eq_pow_sum, ← Finset.card_eq_sum_card_image, Finset.card_univ,
          Fintype.card_fin]


omit hP in
lemma img4 (a b c d : ℕ) : univ.image ![a, b, c, d] = {a, b, c, d} := by
  ext q
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Fin.exists_fin_succ, Fin.exists_fin_zero]
  simp [eq_comm]

omit hP in
lemma cnt4 (a b c d q : ℕ) : #{j | ![a, b, c, d] j = q} =
    (if a = q then 1 else 0) + (if b = q then 1 else 0) + (if c = q then 1 else 0) +
      (if d = q then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_four]
  by_cases h1 : a = q <;> by_cases h2 : b = q <;> by_cases h3 : c = q <;> by_cases h4 : d = q <;>
    simp [h1, h2, h3, h4]

omit hP in
lemma mu_le (a b c d : ℕ) (h0 : ∑ r ∈ J, w r = 0) :
    mu (J := J) (w := w) ![a, b, c, d] ≤
      (if a = b ∧ b = c ∧ c = d then (∑ r ∈ J, w r ^ 4) / a else 0) +
      (if a = b ∧ c = d then (∑ r ∈ J, w r ^ 2) / a * ((∑ r ∈ J, w r ^ 2) / c) else 0) +
      (if a = c ∧ b = d then (∑ r ∈ J, w r ^ 2) / a * ((∑ r ∈ J, w r ^ 2) / b) else 0) +
      (if a = d ∧ b = c then (∑ r ∈ J, w r ^ 2) / a * ((∑ r ∈ J, w r ^ 2) / b) else 0) := by
  have s2 : 0 ≤ ∑ r ∈ J, w r ^ 2 := Finset.sum_nonneg (fun r _ => by positivity)
  have s4 : 0 ≤ ∑ r ∈ J, w r ^ 4 := Finset.sum_nonneg (fun r _ => by positivity)
  have o1 : (b = a) = (a = b) := propext eq_comm
  have o2 : (c = a) = (a = c) := propext eq_comm
  have o3 : (d = a) = (a = d) := propext eq_comm
  have o4 : (c = b) = (b = c) := propext eq_comm
  have o5 : (d = b) = (b = d) := propext eq_comm
  have o6 : (d = c) = (c = d) := propext eq_comm
  rw [mu_def, img4]
  simp_rw [cnt4]
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases had : a = d <;>
    by_cases hbc : b = c <;> by_cases hbd : b = d <;> by_cases hcd : c = d <;>
    simp_all [Finset.prod_insert, Finset.prod_singleton] <;>
    first
    | (apply le_of_eq; ring1)
    | positivity
    | (apply le_add_of_nonneg_right; positivity)
    | (apply le_add_of_nonneg_left; positivity)
    | nlinarith [div_nonneg s2 (Nat.cast_nonneg (α := ℝ) a), div_nonneg s2 (Nat.cast_nonneg (α := ℝ) b),
        div_nonneg s2 (Nat.cast_nonneg (α := ℝ) c), div_nonneg s4 (Nat.cast_nonneg (α := ℝ) a)]

end Model

end OMA.Erdos69Moments

open Finset OMA.Erdos69Moments in
theorem OMA.solution : OMA.R_Erdos69_erdos_69_R2.H2 := by
  intro P J D b M w ⟨hP, h0, h2lo, h2hi, h4, hM⟩ W
  set s := ∑ r ∈ J, |w r| with hs_def
  set σ2 := ∑ r ∈ J, w r ^ 2 with hσ2
  set σ4 := ∑ r ∈ J, w r ^ 4 with hσ4
  set S1 := ∑ p ∈ P, 1 / (p : ℝ) with hS1
  have hs : 0 ≤ s := Finset.sum_nonneg (fun r _ => abs_nonneg _)
  have hσ2n : 0 ≤ σ2 := Finset.sum_nonneg (fun r _ => by positivity)
  have hσ4n : 0 ≤ σ4 := Finset.sum_nonneg (fun r _ => by positivity)
  have hS1n : 0 ≤ S1 := Finset.sum_nonneg (fun p _ => by positivity)
  set c : ℝ := (P.card : ℝ) with hc
  have hcn : 0 ≤ c := Nat.cast_nonneg _
  have hu : 0 ≤ c * s := mul_nonneg hcn hs
  have hE1 : c * s ≤ (1 + c * s) ^ 4 := by
    nlinarith [mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu,
      mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu]
  have hE2 : (c * s) ^ 2 ≤ (1 + c * s) ^ 4 := by nlinarith [sq_nonneg (c * s), mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]
  have hE4 : (c * s) ^ 4 ≤ (1 + c * s) ^ 4 := pow_le_pow_left₀ hu (by linarith) 4
  have hW : ∀ i, W i = ∑ p ∈ P, X J D b w p i := by
    intro i
    simp only [W, X, Finset.mul_sum]
    exact Finset.sum_comm
  refine ⟨?_, ?_, ?_⟩
  · -- first moment
    have h1p : ∀ p ∈ P, |∑ i ∈ range M, X J D b w p i| ≤ s := by
      intro p hp
      have := gen1 (b := b) (w := w) hP M {p} (by simpa using hp) (fun _ => 1) (by simp)
      simpa [h0] using this
    rw [Finset.sum_congr rfl (fun i _ => hW i), Finset.sum_comm]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum h1p).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  · -- second moment
    have hpair : ∀ a ∈ P, ∀ d ∈ P, (if a = d then (M : ℝ) * (σ2 / a) else 0) - s ^ 2 ≤
        ∑ i ∈ range M, X J D b w a i * X J D b w d i := by
      intro a ha d hd
      by_cases had : a = d
      · subst had
        have := gen1 (b := b) (w := w) hP M {a} (by simpa using ha) (fun _ => 2) (by simp)
        have hτ := pow_sum_le (w := w) hP 2 (by norm_num)
        simp only [Finset.prod_singleton] at this
        rw [if_pos rfl]
        have e : ∀ i, X J D b w a i * X J D b w a i = X J D b w a i ^ 2 := fun i => (sq _).symm
        simp_rw [e]
        have := (abs_le.mp this).1
        nlinarith
      · have := gen1 (b := b) (w := w) hP M {a, d} (by intro q hq; simp at hq; rcases hq with rfl | rfl <;> assumption) (fun _ => 1) (by simp)
        simp_rw [Finset.prod_pair had] at this
        simp only [pow_one, h0, zero_div, zero_mul, mul_zero, sub_zero] at this
        rw [if_neg had]
        have := (abs_le.mp this).1
        nlinarith
    have e2 : ∑ i ∈ range M, W i ^ 2 =
        ∑ a ∈ P, ∑ d ∈ P, ∑ i ∈ range M, X J D b w a i * X J D b w d i := by
      simp_rw [hW, sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    rw [e2]
    have hlow := Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun d hd => hpair a ha d hd))
    refine le_trans ?_ hlow
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const, nsmul_eq_mul]
    have hsum : ∑ a ∈ P, (if a ∈ P then (M : ℝ) * (σ2 / a) else 0) = M * (σ2 * S1) := by
      rw [Finset.sum_congr rfl (fun a ha => if_pos ha), hS1, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [hsum]
    have hMn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    nlinarith
  · -- fourth moment
    have e4 : ∀ i, W i ^ 4 = ∑ a ∈ P, ∑ b' ∈ P, ∑ c' ∈ P, ∑ d ∈ P,
        X J D b w a i * X J D b w b' i * X J D b w c' i * X J D b w d i := by
      intro i
      rw [hW, show ∀ x : ℝ, x ^ 4 = x * x * x * x from fun x => by ring]
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ =>
        Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))))
    let H : ℕ → ℕ → ℕ → ℕ → ℝ := fun a b' c' d =>
      (if a = b' ∧ b' = c' ∧ c' = d then σ4 / a else 0) +
      (if a = b' ∧ c' = d then σ2 / a * (σ2 / c') else 0) +
      (if a = c' ∧ b' = d then σ2 / a * (σ2 / b') else 0) +
      (if a = d ∧ b' = c' then σ2 / a * (σ2 / b') else 0)
    have hMn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hq : ∀ a ∈ P, ∀ b' ∈ P, ∀ c' ∈ P, ∀ d ∈ P,
        ∑ i ∈ range M, X J D b w a i * X J D b w b' i * X J D b w c' i * X J D b w d i ≤
          M * H a b' c' d + s ^ 4 := by
      intro a ha b' hb c' hc d hd
      have ht := tuple (b := b) (w := w) hP M 4 ![a, b', c', d]
        (by intro j; fin_cases j <;> assumption)
      have hp : ∀ i, ∏ j, X J D b w (![a, b', c', d] j) i =
          X J D b w a i * X J D b w b' i * X J D b w c' i * X J D b w d i := fun i => by
        simp [Fin.prod_univ_four]
      rw [Finset.sum_congr rfl (fun i _ => hp i)] at ht
      have hmu := mu_le (J := J) (w := w) a b' c' d h0
      have h1 := (abs_le.mp ht).2
      have h2 := mul_le_mul_of_nonneg_left hmu hMn
      rw [← hσ2, ← hσ4] at h2
      rw [← hs_def] at h1
      simp only [H]
      linarith
    have hsumH : ∑ a ∈ P, ∑ b' ∈ P, ∑ c' ∈ P, ∑ d ∈ P, H a b' c' d =
        σ4 * S1 + 3 * (σ2 * S1) ^ 2 := by
      simp only [H, Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.sum_const_zero, Finset.sum_ite_mem, Finset.inter_self]
      have k1 : ∑ x ∈ P, σ4 / (x : ℝ) = σ4 * S1 := by
        rw [hS1, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      have k2 : ∑ x ∈ P, ∑ y ∈ P, σ2 / (x : ℝ) * (σ2 / y) = (σ2 * S1) ^ 2 := by
        rw [sq, hS1, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => by ring)
      rw [k1, k2]
      ring
    have hfin : ∑ i ∈ range M, W i ^ 4 ≤
        ∑ a ∈ P, ∑ b' ∈ P, ∑ c' ∈ P, ∑ d ∈ P, ((M : ℝ) * H a b' c' d + s ^ 4) := by
      rw [Finset.sum_congr rfl (fun i _ => e4 i), Finset.sum_comm]
      refine Finset.sum_le_sum (fun a ha => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum (fun b' hb => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum (fun c' hc => ?_)
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum (fun d hd => hq a ha b' hb c' hc d hd)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hfin
    rw [hsumH] at hfin
    have hsq : (σ2 * S1) ^ 2 ≤ (11 / 10000) ^ 2 := pow_le_pow_left₀ (by linarith) h2hi 2
    have hc4 : c * (c * (c * (c * s ^ 4))) = (c * s) ^ 4 := by ring
    nlinarith
