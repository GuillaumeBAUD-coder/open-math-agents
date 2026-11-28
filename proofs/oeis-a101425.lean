import OMAStatements.S_oeis_a101425
import Mathlib

/-! Proof for OEIS A101425: Burnside's lemma for `S₃` permuting ordered factor triples; each orbit
contains exactly one sorted triple (`Tuple.sort`). Writing the factors as `p^(u_i) q^(w_i)`, the
identity fixes `C(5+2, 2) * C(n+2, 2)` triples, each transposition fixes `(5/2 + 1)(⌊n/2⌋ + 1)`,
and the 3-cycles fix none since `3 ∤ 5`; hence `6 a(n) = C(5+2,2) C(n+2,2) + 3 * 3 (⌊n/2⌋ + 1)`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P101425
open OMA.S_oeis_a101425 Equiv

abbrev G := Perm (Fin 3)

/-- ordered triples with product `V`. -/
def T (V : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ => V.divisors).filter (fun f => ∏ i, f i = V)

lemma mem_T {V : ℕ} {f : Fin 3 → ℕ} : f ∈ T V ↔ V ≠ 0 ∧ ∏ i, f i = V := by
  simp only [T, Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨(h 0).2, hp⟩
  · rintro ⟨h0, hp⟩
    refine ⟨fun i => ⟨?_, h0⟩, hp⟩
    rw [← hp]; exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)

abbrev X (V : ℕ) := {f : Fin 3 → ℕ // f ∈ T V}

lemma comp_mem {V : ℕ} (σ : G) {f : Fin 3 → ℕ} (hf : f ∈ T V) : f ∘ σ.symm ∈ T V := by
  rw [mem_T] at hf ⊢
  refine ⟨hf.1, ?_⟩
  rw [← hf.2]; exact Equiv.prod_comp σ.symm f

instance act (V : ℕ) : MulAction G (X V) where
  smul σ x := ⟨x.1 ∘ σ.symm, comp_mem σ x.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

lemma smul_val {V : ℕ} (σ : G) (x : X V) : (σ • x).1 = x.1 ∘ σ.symm := rfl

lemma mono_iff (f : Fin 3 → ℕ) : Monotone f ↔ f 0 ≤ f 1 ∧ f 1 ≤ f 2 := by
  rw [Fin.monotone_iff_le_succ]
  constructor
  · intro h; exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h1, h2⟩ i; fin_cases i <;> simpa

/-! ## Orbits are sorted triples -/

open Classical in
lemma orbits_eq (V : ℕ) : Fintype.card (MulAction.orbitRel.Quotient G (X V)) =
    (Finset.univ.filter (fun x : X V => Monotone x.1)).card := by
  symm
  rw [← Finset.card_univ (α := MulAction.orbitRel.Quotient G (X V))]
  apply Finset.card_bij (fun x _ => (Quotient.mk _ x : MulAction.orbitRel.Quotient G (X V)))
  · intros; exact Finset.mem_univ _
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have h : x ∈ MulAction.orbit G y := Quotient.exact hxy
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1 h
    apply Subtype.ext
    have e1 : x.1 = y.1 ∘ σ.symm := by rw [← hσ]; rfl
    have hx' : Monotone (y.1 ∘ ⇑σ.symm) := e1 ▸ hx
    have k1 := (Tuple.comp_sort_eq_comp_iff_monotone (f := y.1) (σ := σ.symm)).2 hx'
    have k2 := (Tuple.comp_sort_eq_comp_iff_monotone (f := y.1) (σ := 1)).2 (by simpa using hy)
    rw [e1, k1, ← k2]; rfl
  · intro c _
    induction c using Quotient.inductionOn with
    | h x =>
      refine ⟨(Tuple.sort x.1)⁻¹ • x, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [smul_val, Equiv.Perm.inv_def, Equiv.symm_symm]
        exact Tuple.monotone_sort x.1
      · apply Quotient.sound
        exact ⟨(Tuple.sort x.1)⁻¹, rfl⟩

open Classical in
lemma sorted_eq (V : ℕ) :
    (Finset.univ.filter (fun x : X V => Monotone x.1)).card = cuboids V := by
  unfold cuboids
  refine Finset.card_bij' (fun x _ => (x.1 0, x.1 1, x.1 2))
    (fun t ht => ⟨![t.1, t.2.1, t.2.2], by
      simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at ht
      rw [mem_T, Fin.prod_univ_three]
      exact ⟨ht.1.1.2, by simpa using ht.2.2.2⟩⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mono_iff] at hx
    have hT := mem_T.1 x.2
    rw [Fin.prod_univ_three] at hT
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
    refine ⟨⟨⟨?_, hT.1⟩, ⟨?_, hT.1⟩, ⟨?_, hT.1⟩⟩, hx.1, hx.2, hT.2⟩
    · exact Dvd.intro (x.1 1 * x.1 2) (by rw [← mul_assoc]; exact hT.2)
    · exact Dvd.intro (x.1 0 * x.1 2) (by rw [show x.1 1 * (x.1 0 * x.1 2) = x.1 0 * x.1 1 * x.1 2 by ring]; exact hT.2)
    · exact Dvd.intro_left (x.1 0 * x.1 1) hT.2
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_product] at ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mono_iff]
    simpa using ⟨ht.2.1, ht.2.2.1⟩
  · intro x _
    apply Subtype.ext
    funext i; fin_cases i <;> rfl
  · intro t _; rfl

/-! ## Exponent triples -/

def U (e : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (e + 1)).filter (fun u => ∑ i, u i = e)

lemma mem_U {e : ℕ} {u : Fin 3 → ℕ} : u ∈ U e ↔ ∑ i, u i = e := by
  simp only [U, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨fun i => ?_, h⟩
    have := Finset.single_le_sum (f := u) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

open Classical in
noncomputable def fixU (e : ℕ) (σ : G) : ℕ := ((U e).filter (fun u => u ∘ σ.symm = u)).card

lemma card_U (e : ℕ) : 2 * (U e).card = (e + 1) * (e + 2) := by
  have h1 : (U e).card = ((Finset.range (e + 1)).sigma (fun a => Finset.range (e - a + 1))).card := by
    apply Finset.card_nbij' (fun u => ⟨u 0, u 1⟩) (fun s => ![s.1, s.2, e - s.1 - s.2])
    · intro u hu
      rw [Finset.mem_coe, mem_U, Fin.sum_univ_three] at hu
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]; omega
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hs
      rw [Finset.mem_coe, mem_U, Fin.sum_univ_three]
      simp; omega
    · intro u hu
      rw [Finset.mem_coe, mem_U, Fin.sum_univ_three] at hu
      funext i; fin_cases i <;> simp; omega
    · intro s _; rfl
  rw [h1, Finset.card_sigma]
  clear h1
  simp only [Finset.card_range]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.sub_self,
      Finset.sum_congr rfl (fun a ha => show e + 1 - a + 1 = (e - a + 1) + 1 by
        simp only [Finset.mem_range] at ha; omega),
      Finset.sum_add_distrib, mul_add, mul_add, ih]
    simp; ring

lemma cover (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : Fin 3) :
    t = i ∨ t = j ∨ t = k := by
  have := i.isLt; have := j.isLt; have := k.isLt; have := t.isLt
  rw [Ne, Fin.ext_iff] at hij hik hjk
  rw [Fin.ext_iff, Fin.ext_iff, Fin.ext_iff]; omega

lemma sum3 (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Fin 3 → ℕ) :
    ∑ t, u t = u i + u j + u k := by
  have : (Finset.univ : Finset (Fin 3)) = {i, j, k} := by
    ext t; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact cover i j k hij hik hjk t
  rw [this, Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
    Finset.sum_singleton, add_assoc]

lemma swap_fix_iff (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u : Fin 3 → ℕ) :
    u ∘ (swap i j).symm = u ↔ u i = u j := by
  rw [Equiv.symm_swap]
  constructor
  · intro h
    have := congrFun h i
    simp only [Function.comp, swap_apply_left] at this
    exact this.symm
  · intro h; funext t
    simp only [Function.comp]
    rcases cover i j k hij hik hjk t with rfl | rfl | rfl
    · rw [swap_apply_left, h]
    · rw [swap_apply_right, h]
    · rw [swap_apply_of_ne_of_ne hik.symm hjk.symm]

open Classical in
lemma fixU_swap (e : ℕ) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    fixU e (swap i j) = e / 2 + 1 := by
  unfold fixU
  rw [← Finset.card_range (e / 2 + 1)]
  apply Finset.card_nbij' (fun u => u i) (fun a => fun t => if t = k then e - 2 * a else a)
  · intro u hu
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_U, swap_fix_iff i j k hij hik hjk,
      sum3 i j k hij hik hjk] at hu
    simp only [Finset.coe_range, Set.mem_Iio]; omega
  · intro a ha
    simp only [Finset.coe_range, Set.mem_Iio] at ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_U, swap_fix_iff i j k hij hik hjk,
      sum3 i j k hij hik hjk, if_neg hik, if_neg hjk, if_true, and_true]
    omega
  · intro u hu
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_U, swap_fix_iff i j k hij hik hjk,
      sum3 i j k hij hik hjk] at hu
    funext t
    rcases cover i j k hij hik hjk t with rfl | rfl | rfl
    · simp [if_neg hik]
    · simp [if_neg hjk, hu.2]
    · simp only [if_true, ite_true]; omega
  · intro a _
    simp [if_neg hik]

open Classical in
lemma fixU_cyc (e : ℕ) (hne : ¬ 3 ∣ e) (σ : G)
    (hσ : (σ.symm 0 = 2 ∧ σ.symm 1 = 0 ∧ σ.symm 2 = 1) ∨ (σ.symm 0 = 1 ∧ σ.symm 1 = 2 ∧ σ.symm 2 = 0)) :
    fixU e σ = 0 := by
  unfold fixU
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu hfix
  rw [mem_U, Fin.sum_univ_three] at hu
  have h0 := congrFun hfix 0
  have h1 := congrFun hfix 1
  simp only [Function.comp] at h0 h1
  rcases hσ with ⟨a, b, -⟩ | ⟨a, b, -⟩ <;> rw [a] at h0 <;> rw [b] at h1 <;>
    exact hne ⟨u 0, by omega⟩

/-! ## Transport to exponents -/

section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
include hp hq hpq

lemma fact_p (a b : ℕ) : (p ^ a * q ^ b).factorization p = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    hp.factorization_pow, hq.factorization_pow]
  simp [Finsupp.single_apply, Ne.symm hpq]

lemma fact_q (a b : ℕ) : (p ^ a * q ^ b).factorization q = b := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    hp.factorization_pow, hq.factorization_pow]
  simp [Finsupp.single_apply, hpq]

lemma dvd_form {d e n : ℕ} (h : d ∣ p ^ e * q ^ n) :
    p ^ (d.factorization p) * q ^ (d.factorization q) = d := by
  obtain ⟨y, z, hy, hz, rfl⟩ := dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hy
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hz
  rw [fact_p hp hq hpq, fact_q hp hq hpq]

open Classical in
lemma fix_eq (e n : ℕ) (σ : G) :
    (Finset.univ.filter (fun x : X (p ^ e * q ^ n) => σ • x = x)).card = fixU e σ * fixU n σ := by
  have hV : p ^ e * q ^ n ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  unfold fixU
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun x _ => (fun k => (x.1 k).factorization p, fun k => (x.1 k).factorization q))
    (fun uw huw => ⟨fun k => p ^ uw.1 k * q ^ uw.2 k, by
      simp only [Finset.mem_product, Finset.mem_filter, mem_U] at huw
      rw [mem_T, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        huw.1.1, huw.2.1]
      exact ⟨hV, rfl⟩⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hT := mem_T.1 x.2
    have hne : ∀ k ∈ Finset.univ, x.1 k ≠ 0 := fun k _ h => by
      have := Finset.prod_eq_zero (Finset.mem_univ k) h; rw [hT.2] at this; exact hV this
    have hfac := congrArg Nat.factorization hT.2
    rw [Nat.factorization_prod hne] at hfac
    have hfix : x.1 ∘ σ.symm = x.1 := congrArg Subtype.val hx
    simp only [Finset.mem_product, Finset.mem_filter, mem_U]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := congrArg (fun f => f p) hfac
      simpa [Finsupp.finsetSum_apply, fact_p hp hq hpq] using this
    · funext k; exact congrArg (fun d => d.factorization p) (congrFun hfix k)
    · have := congrArg (fun f => f q) hfac
      simpa [Finsupp.finsetSum_apply, fact_q hp hq hpq] using this
    · funext k; exact congrArg (fun d => d.factorization q) (congrFun hfix k)
  · intro uw huw
    simp only [Finset.mem_product, Finset.mem_filter] at huw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Subtype.ext
    rw [smul_val]
    funext k
    have h1 := congrFun huw.1.2 k
    have h2 := congrFun huw.2.2 k
    simp only [Function.comp] at h1 h2
    show p ^ uw.1 (σ.symm k) * q ^ uw.2 (σ.symm k) = p ^ uw.1 k * q ^ uw.2 k
    rw [h1, h2]
  · intro x _
    apply Subtype.ext; funext k
    have hT := mem_T.1 x.2
    have hd : x.1 k ∣ p ^ e * q ^ n := by
      have := Finset.dvd_prod_of_mem (fun i => x.1 i) (Finset.mem_univ k)
      rwa [hT.2] at this
    exact dvd_form hp hq hpq hd
  · intro uw _
    ext k
    · exact fact_p hp hq hpq _ _
    · exact fact_q hp hq hpq _ _

open Classical in
lemma burnside (e n : ℕ) (he : ¬ 3 ∣ e) :
    cuboids (p ^ e * q ^ n) * 6 = fixU e 1 * fixU n 1 + 3 * ((e / 2 + 1) * (n / 2 + 1)) := by
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (X (p ^ e * q ^ n))
  have hG : Fintype.card G = 6 := by rw [Fintype.card_perm, Fintype.card_fin]; rfl
  have hfix : ∀ g : G, Fintype.card (MulAction.fixedBy (X (p ^ e * q ^ n)) g) =
      fixU e g * fixU n g := by
    intro g
    rw [← fix_eq hp hq hpq e n g, ← Fintype.card_subtype]; rfl
  have huniv : (Finset.univ : Finset G) =
      {1, swap 0 1, swap 0 2, swap 1 2, finRotate 3, finRotate 3 * finRotate 3} := by decide
  rw [hG] at hb
  simp only [hfix] at hb
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    fixU_swap e 0 1 2 (by decide) (by decide) (by decide),
    fixU_swap n 0 1 2 (by decide) (by decide) (by decide),
    fixU_swap e 0 2 1 (by decide) (by decide) (by decide),
    fixU_swap n 0 2 1 (by decide) (by decide) (by decide),
    fixU_swap e 1 2 0 (by decide) (by decide) (by decide),
    fixU_swap n 1 2 0 (by decide) (by decide) (by decide),
    fixU_cyc e he (finRotate 3) (Or.inl (by decide)),
    fixU_cyc e he (finRotate 3 * finRotate 3) (Or.inr (by decide))] at hb
  rw [← sorted_eq, ← orbits_eq]
  change _ = Fintype.card (MulAction.orbitRel.Quotient G (X (p ^ e * q ^ n))) * 6 at hb
  rw [← hb]
  ring

end

lemma fixU_one (e : ℕ) : 2 * fixU e 1 = (e + 1) * (e + 2) := by
  classical
  unfold fixU
  convert card_U e using 3
  apply Finset.filter_true_of_mem
  intro u _; rfl

end OMA.P101425

theorem OMA.solution : type_of% @OMA.S_oeis_a101425.main := by
  intro p q hp hq hpq n
  have hb := OMA.P101425.burnside hp hq hpq 5 n (by norm_num)
  have h4 := OMA.P101425.fixU_one 5
  have hn := OMA.P101425.fixU_one n
  have h4' : OMA.P101425.fixU 5 1 = 21 := by omega
  rw [h4'] at hb
  norm_num at hb
  have hz : (OMA.S_oeis_a101425.cuboids (p ^ 5 * q ^ n) : ℤ) * 12 =
      21 * ((n + 1) * (n + 2)) + 18 * ((n / 2 : ℕ) + 1) := by
    have : OMA.S_oeis_a101425.cuboids (p ^ 5 * q ^ n) * 12 =
        21 * (2 * OMA.P101425.fixU n 1) + 18 * (n / 2 + 1) := by omega
    rw [hn] at this
    exact_mod_cast this
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow]
    obtain ⟨m, rfl⟩ := he
    rw [show (m + m) / 2 = m by omega] at hz
    push_cast at hz ⊢
    linarith
  · rw [ho.neg_one_pow]
    obtain ⟨m, rfl⟩ := ho
    rw [show (2 * m + 1) / 2 = m by omega] at hz
    push_cast at hz ⊢
    linarith
