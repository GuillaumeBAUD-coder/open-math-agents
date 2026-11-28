import FormalConjectures.Wikipedia.PierceBirkhoff
import Mathlib

/-!
# Mahé's 2-dimensional Pierce-Birkhoff theorem

Elementary proof following Mahé (1984) and Delzell's exposition (arXiv:1002.0038):
- Closure of finite sup-inf of bivariate polynomials (`SI`) under `+`, `-`, `max`, `min`, and
  multiplication by arbitrary polynomials (via `p = ((p + 1) / 2)^2 - ((p - 1) / 2)^2`),
- 2D polynomial root separation (`projection_poly`) via squarefree decomposition in `(RatFunc ℝ)[Y]`
  and elementary simple-root continuity (Cauchy root bound + IVT + strict monotonicity),
- Mahé's truncation lemma (`mahe_truncation`) by induction on `y`-degree and root index,
- Vertical and horizontal strip representatives, Mahé's diagonal-strip separator with odd degree
  `e = 2 * deg + 1`, and global density/continuity assembly.
-/

namespace OMAPB2

open MvPolynomial Polynomial

/- ## Part 1: Finite sup-inf of bivariate polynomials (`SI`) -/

def SI (f : (Fin 2 → ℝ) → ℝ) : Prop :=
  ∃ (ι κ : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : Fintype κ) (_ : Nonempty κ)
    (g : ι → κ → MvPolynomial (Fin 2) ℝ),
    ∀ x, f x = ⨆ i, ⨅ j, MvPolynomial.eval x (g i j)

lemma supinf_eq {ι κ : Type} [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
    (a : ι → κ → ℝ) (y : ℝ) (h1 : ∀ i, ∃ j, a i j ≤ y) (h2 : ∃ i, ∀ j, y ≤ a i j) :
    ⨆ i, ⨅ j, a i j = y := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    obtain ⟨j, hj⟩ := h1 i
    exact (ciInf_le (Set.finite_range _).bddBelow j).trans hj
  · obtain ⟨i, hi⟩ := h2
    exact (le_ciInf hi).trans (le_ciSup (Set.finite_range (fun i => ⨅ j, a i j)).bddAbove i)

lemma continuous_finset_inf' {α β : Type*} [TopologicalSpace β]
    {s : Finset α} (hs : s.Nonempty) (F : α → β → ℝ) (hF : ∀ a ∈ s, Continuous (F a)) :
    Continuous (fun x => s.inf' hs (fun a => F a x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hF a (Finset.mem_singleton_self a)
  | cons a s has hs ih =>
    have heq : (fun x => (Finset.cons a s has).inf' (Finset.cons_nonempty has) (fun b => F b x)) =
        fun x => min (F a x) (s.inf' hs (fun b => F b x)) := by
      funext x; exact Finset.inf'_cons hs (fun b => F b x)
    rw [heq]
    exact (hF a (Finset.mem_cons_self a s)).min (ih fun b hb => hF b (Finset.mem_cons_of_mem hb))

lemma continuous_finset_sup' {α β : Type*} [TopologicalSpace β]
    {s : Finset α} (hs : s.Nonempty) (F : α → β → ℝ) (hF : ∀ a ∈ s, Continuous (F a)) :
    Continuous (fun x => s.sup' hs (fun a => F a x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hF a (Finset.mem_singleton_self a)
  | cons a s has hs ih =>
    have heq : (fun x => (Finset.cons a s has).sup' (Finset.cons_nonempty has) (fun b => F b x)) =
        fun x => max (F a x) (s.sup' hs (fun b => F b x)) := by
      funext x; exact Finset.sup'_cons hs (fun b => F b x)
    rw [heq]
    exact (hF a (Finset.mem_cons_self a s)).max (ih fun b hb => hF b (Finset.mem_cons_of_mem hb))

lemma SI_continuous {f : (Fin 2 → ℝ) → ℝ} (hf : SI f) : Continuous f := by
  obtain ⟨ι, κ, _, _, _, _, g, hg⟩ := hf
  have : f = fun x => ⨆ i, ⨅ j, MvPolynomial.eval x (g i j) := funext hg
  rw [this]
  have h1 : ∀ i, Continuous (fun x => ⨅ j, MvPolynomial.eval x (g i j)) := by
    intro i
    have heq : (fun x => ⨅ j, MvPolynomial.eval x (g i j)) =
        fun x => Finset.univ.inf' Finset.univ_nonempty (fun j => MvPolynomial.eval x (g i j)) := by
      funext x
      apply le_antisymm
      · rw [Finset.le_inf'_iff]
        intro j _
        exact ciInf_le (Set.finite_range _).bddBelow j
      · apply le_ciInf
        intro j
        exact Finset.inf'_le _ (Finset.mem_univ j)
    rw [heq]
    exact continuous_finset_inf' Finset.univ_nonempty _ (fun j _ => MvPolynomial.continuous_eval _)
  have heq2 : (fun x => ⨆ i, ⨅ j, MvPolynomial.eval x (g i j)) =
      fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => ⨅ j, MvPolynomial.eval x (g i j)) := by
    funext x
    apply le_antisymm
    · apply ciSup_le
      intro i
      exact Finset.le_sup' (fun i => ⨅ j, MvPolynomial.eval x (g i j)) (Finset.mem_univ i)
    · rw [Finset.sup'_le_iff]
      intro i _
      exact le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (g i j))).bddAbove i
  rw [heq2]
  exact continuous_finset_sup' Finset.univ_nonempty _ (fun i _ => h1 i)

lemma SI_poly (p : MvPolynomial (Fin 2) ℝ) : SI (fun x => MvPolynomial.eval x p) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ _ => p, fun x => ?_⟩
  rw [supinf_eq (fun _ _ => MvPolynomial.eval x p) (MvPolynomial.eval x p)
    (fun _ => ⟨(), le_rfl⟩) ⟨(), fun _ => le_rfl⟩]

lemma SI_add {f g : (Fin 2 → ℝ) → ℝ} (hf : SI f) (hg : SI g) : SI (fun x => f x + g x) := by
  obtain ⟨ι₁, κ₁, _, _, _, _, a, ha⟩ := hf
  obtain ⟨ι₂, κ₂, _, _, _, _, b, hb⟩ := hg
  refine ⟨ι₁ × ι₂, κ₁ × κ₂, inferInstance, inferInstance, inferInstance, inferInstance,
    fun p q => a p.1 q.1 + b p.2 q.2, fun x => ?_⟩
  show f x + g x = _
  rw [ha x, hb x]
  symm
  apply supinf_eq
  · rintro ⟨i, k⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j => MvPolynomial.eval x (a i j))
    obtain ⟨l, hl⟩ := exists_eq_ciInf_of_finite (f := fun l => MvPolynomial.eval x (b k l))
    refine ⟨(j, l), ?_⟩
    simp only [map_add]
    apply add_le_add
    · rw [hj]; exact le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (a i j))).bddAbove i
    · rw [hl]; exact le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (b i j))).bddAbove k
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨅ j, MvPolynomial.eval x (a i j))
    obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => ⨅ l, MvPolynomial.eval x (b k l))
    refine ⟨(i, k), ?_⟩
    rintro ⟨j, l⟩
    simp only [map_add]
    rw [← hi, ← hk]
    exact add_le_add (ciInf_le (Set.finite_range _).bddBelow j)
      (ciInf_le (Set.finite_range _).bddBelow l)

lemma SI_sup {f g : (Fin 2 → ℝ) → ℝ} (hf : SI f) (hg : SI g) :
    SI (fun x => max (f x) (g x)) := by
  obtain ⟨ι₁, κ₁, _, _, _, _, a, ha⟩ := hf
  obtain ⟨ι₂, κ₂, _, _, _, _, b, hb⟩ := hg
  refine ⟨ι₁ ⊕ ι₂, κ₁ × κ₂, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i j => Sum.elim (fun i₁ => a i₁ j.1) (fun i₂ => b i₂ j.2) i, fun x => ?_⟩
  symm
  apply supinf_eq
  · rintro (i₁ | i₂)
    · obtain ⟨j₁, hj₁⟩ := exists_eq_ciInf_of_finite (f := fun j => MvPolynomial.eval x (a i₁ j))
      obtain ⟨j₂⟩ := ‹Nonempty κ₂›
      refine ⟨(j₁, j₂), ?_⟩
      simp only [Sum.elim_inl]
      rw [hj₁, ha x]
      exact (le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (a i j))).bddAbove i₁).trans
        (le_max_left _ _)
    · obtain ⟨j₁⟩ := ‹Nonempty κ₁›
      obtain ⟨j₂, hj₂⟩ := exists_eq_ciInf_of_finite (f := fun j => MvPolynomial.eval x (b i₂ j))
      refine ⟨(j₁, j₂), ?_⟩
      simp only [Sum.elim_inr]
      rw [hj₂, hb x]
      exact (le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (b i j))).bddAbove i₂).trans
        (le_max_right _ _)
  · dsimp only
    rcases le_total (f x) (g x) with hfg | hgf
    · rw [max_eq_right hfg, hb x]
      obtain ⟨i₂, hi₂⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨅ j, MvPolynomial.eval x (b i j))
      refine ⟨Sum.inr i₂, fun j => ?_⟩
      simp only [Sum.elim_inr]
      rw [← hi₂]
      exact ciInf_le (Set.finite_range _).bddBelow j.2
    · rw [max_eq_left hgf, ha x]
      obtain ⟨i₁, hi₁⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨅ j, MvPolynomial.eval x (a i j))
      refine ⟨Sum.inl i₁, fun j => ?_⟩
      simp only [Sum.elim_inl]
      rw [← hi₁]
      exact ciInf_le (Set.finite_range _).bddBelow j.1

lemma SI_inf {f g : (Fin 2 → ℝ) → ℝ} (hf : SI f) (hg : SI g) :
    SI (fun x => min (f x) (g x)) := by
  obtain ⟨ι₁, κ₁, _, _, _, _, a, ha⟩ := hf
  obtain ⟨ι₂, κ₂, _, _, _, _, b, hb⟩ := hg
  refine ⟨ι₁ × ι₂, κ₁ ⊕ κ₂, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i j => Sum.elim (fun j₁ => a i.1 j₁) (fun j₂ => b i.2 j₂) j, fun x => ?_⟩
  symm
  apply supinf_eq
  · rintro ⟨i₁, i₂⟩
    dsimp only
    rcases le_total (f x) (g x) with hfg | hgf
    · rw [min_eq_left hfg, ha x]
      obtain ⟨j₁, hj₁⟩ := exists_eq_ciInf_of_finite (f := fun j => MvPolynomial.eval x (a i₁ j))
      refine ⟨Sum.inl j₁, ?_⟩
      simp only [Sum.elim_inl]
      rw [hj₁]
      exact le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (a i j))).bddAbove i₁
    · rw [min_eq_right hgf, hb x]
      obtain ⟨j₂, hj₂⟩ := exists_eq_ciInf_of_finite (f := fun j => MvPolynomial.eval x (b i₂ j))
      refine ⟨Sum.inr j₂, ?_⟩
      simp only [Sum.elim_inr]
      rw [hj₂]
      exact le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (b i j))).bddAbove i₂
  · obtain ⟨i₁, hi₁⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨅ j, MvPolynomial.eval x (a i j))
    obtain ⟨i₂, hi₂⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨅ j, MvPolynomial.eval x (b i j))
    refine ⟨(i₁, i₂), fun j => ?_⟩
    rcases j with j₁ | j₂
    · simp only [Sum.elim_inl]
      calc min (f x) (g x) ≤ f x := min_le_left _ _
        _ = ⨅ j, MvPolynomial.eval x (a i₁ j) := by rw [ha x, ← hi₁]
        _ ≤ MvPolynomial.eval x (a i₁ j₁) := ciInf_le (Set.finite_range _).bddBelow j₁
    · simp only [Sum.elim_inr]
      calc min (f x) (g x) ≤ g x := min_le_right _ _
        _ = ⨅ j, MvPolynomial.eval x (b i₂ j) := by rw [hb x, ← hi₂]
        _ ≤ MvPolynomial.eval x (b i₂ j₂) := ciInf_le (Set.finite_range _).bddBelow j₂

lemma SI_neg {f : (Fin 2 → ℝ) → ℝ} (hf : SI f) : SI (fun x => -f x) := by
  classical
  obtain ⟨ι, κ, _, _, _, _, a, ha⟩ := hf
  refine ⟨ι → κ, ι, inferInstance, inferInstance, inferInstance, inferInstance,
    fun φ i => -a i (φ i), fun x => ?_⟩
  symm
  apply supinf_eq
  · intro φ
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨅ j, MvPolynomial.eval x (a i j))
    refine ⟨i, ?_⟩
    simp only [map_neg]
    rw [neg_le_neg_iff, ha x, ← hi]
    exact ciInf_le (Set.finite_range _).bddBelow (φ i)
  · have hmin : ∀ i, ∃ j, MvPolynomial.eval x (a i j) = ⨅ k, MvPolynomial.eval x (a i k) :=
      fun i => exists_eq_ciInf_of_finite (f := fun k => MvPolynomial.eval x (a i k))
    choose φ hφ using hmin
    refine ⟨φ, fun i => ?_⟩
    simp only [map_neg]
    rw [neg_le_neg_iff, hφ i, ha x]
    exact le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (a i j))).bddAbove i

lemma SI_mul_nonneg_poly (q : MvPolynomial (Fin 2) ℝ)
    (hq : ∀ x, 0 ≤ MvPolynomial.eval x q) {f : (Fin 2 → ℝ) → ℝ} (hf : SI f) :
    SI (fun x => MvPolynomial.eval x q * f x) := by
  obtain ⟨ι, κ, _, _, _, _, a, ha⟩ := hf
  refine ⟨ι, κ, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i j => q * a i j, fun x => ?_⟩
  symm
  apply supinf_eq
  · intro i
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j => MvPolynomial.eval x (a i j))
    refine ⟨j, ?_⟩
    simp only [map_mul]
    apply mul_le_mul_of_nonneg_left _ (hq x)
    rw [hj, ha x]
    exact le_ciSup (Set.finite_range (fun i => ⨅ j, MvPolynomial.eval x (a i j))).bddAbove i
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => ⨅ j, MvPolynomial.eval x (a i j))
    refine ⟨i, fun j => ?_⟩
    simp only [map_mul]
    apply mul_le_mul_of_nonneg_left _ (hq x)
    rw [ha x, ← hi]
    exact ciInf_le (Set.finite_range _).bddBelow j

lemma SI_mul_poly (p : MvPolynomial (Fin 2) ℝ) {f : (Fin 2 → ℝ) → ℝ} (hf : SI f) :
    SI (fun x => MvPolynomial.eval x p * f x) := by
  set u : MvPolynomial (Fin 2) ℝ := MvPolynomial.C (1 / 2 : ℝ) * (p + 1)
  set v : MvPolynomial (Fin 2) ℝ := MvPolynomial.C (1 / 2 : ℝ) * (p - 1)
  have hu : ∀ x, 0 ≤ MvPolynomial.eval x (u * u) := fun x => by
    simp only [map_mul]; exact mul_self_nonneg _
  have hv : ∀ x, 0 ≤ MvPolynomial.eval x (v * v) := fun x => by
    simp only [map_mul]; exact mul_self_nonneg _
  have h1 := SI_mul_nonneg_poly (u * u) hu hf
  have h2 := SI_mul_nonneg_poly (v * v) hv (SI_neg hf)
  have h3 := SI_add h1 h2
  have heq : (fun x => MvPolynomial.eval x (u * u) * f x + MvPolynomial.eval x (v * v) * (-f x)) =
      fun x => MvPolynomial.eval x p * f x := by
    funext x
    simp only [u, v, map_mul, map_add, map_sub, map_one, MvPolynomial.eval_C]
    ring
  rwa [heq] at h3

lemma SI_swap {f : (Fin 2 → ℝ) → ℝ} (hf : SI f) :
    SI (fun x => f (fun i => x (1 - i))) := by
  obtain ⟨ι, κ, _, _, _, _, a, ha⟩ := hf
  refine ⟨ι, κ, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i j => MvPolynomial.rename (fun k : Fin 2 => 1 - k) (a i j), fun x => ?_⟩
  dsimp only
  rw [ha]
  congr 1; ext i; congr 1; ext j
  simp [MvPolynomial.eval_rename, Function.comp_def]

lemma SI_finset_sum {α : Type*} (s : Finset α) (F : α → (Fin 2 → ℝ) → ℝ)
    (hF : ∀ a ∈ s, SI (F a)) : SI (fun x => ∑ a ∈ s, F a x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using SI_poly 0
  | @insert a s has ih =>
    have heq : (fun x => ∑ b ∈ insert a s, F b x) = fun x => F a x + ∑ b ∈ s, F b x := by
      funext x; exact Finset.sum_insert has
    rw [heq]
    exact SI_add (hF a (Finset.mem_insert_self a s))
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

lemma SI_finset_sup' {α : Type*} {s : Finset α} (hs : s.Nonempty) (F : α → (Fin 2 → ℝ) → ℝ)
    (hF : ∀ a ∈ s, SI (F a)) : SI (fun x => s.sup' hs (fun a => F a x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hF a (Finset.mem_singleton_self a)
  | cons a s has hs ih =>
    have heq : (fun x => (Finset.cons a s has).sup' (Finset.cons_nonempty has) (fun b => F b x)) =
        fun x => max (F a x) (s.sup' hs (fun b => F b x)) := by
      funext x; exact Finset.sup'_cons hs (fun b => F b x)
    rw [heq]
    exact SI_sup (hF a (Finset.mem_cons_self a s))
      (ih fun b hb => hF b (Finset.mem_cons_of_mem hb))

lemma SI_finset_inf' {α : Type*} {s : Finset α} (hs : s.Nonempty) (F : α → (Fin 2 → ℝ) → ℝ)
    (hF : ∀ a ∈ s, SI (F a)) : SI (fun x => s.inf' hs (fun a => F a x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hF a (Finset.mem_singleton_self a)
  | cons a s has hs ih =>
    have heq : (fun x => (Finset.cons a s has).inf' (Finset.cons_nonempty has) (fun b => F b x)) =
        fun x => min (F a x) (s.inf' hs (fun b => F b x)) := by
      funext x; exact Finset.inf'_cons hs (fun b => F b x)
    rw [heq]
    exact SI_inf (hF a (Finset.mem_cons_self a s))
      (ih fun b hb => hF b (Finset.mem_cons_of_mem hb))

/- ## Part 2: Conversion `MvPolynomial (Fin 2) ℝ ≃ Polynomial (Polynomial ℝ)` -/

noncomputable def toPolyY : MvPolynomial (Fin 2) ℝ →+* Polynomial (Polynomial ℝ) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun i => if i = 0 then Polynomial.C Polynomial.X else Polynomial.X)

noncomputable def fromPolyY : Polynomial (Polynomial ℝ) →+* MvPolynomial (Fin 2) ℝ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (MvPolynomial.X 1)

lemma fromPolyY_toPolyY (p : MvPolynomial (Fin 2) ℝ) : fromPolyY (toPolyY p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [toPolyY, fromPolyY]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    fin_cases i <;> simp [toPolyY, fromPolyY]

lemma eval_toPolyY (p : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    ((toPolyY p).map (Polynomial.evalRingHom (x 0))).eval (x 1) = MvPolynomial.eval x p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [toPolyY]
  | add p q hp hq => rw [map_add, Polynomial.map_add, Polynomial.eval_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.map_mul, Polynomial.eval_mul, map_mul, hp]
    fin_cases i <;> simp [toPolyY]

lemma eval_fromPolyY (P : Polynomial (Polynomial ℝ)) (x : Fin 2 → ℝ) :
    MvPolynomial.eval x (fromPolyY P) = (P.map (Polynomial.evalRingHom (x 0))).eval (x 1) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, Polynomial.map_add, Polynomial.eval_add, hp, hq]
  | monomial n a =>
    simp only [fromPolyY, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      Polynomial.map_monomial, Polynomial.eval_monomial, map_mul, map_pow, MvPolynomial.eval_X,
      Polynomial.coe_evalRingHom]
    congr 1
    induction a using Polynomial.induction_on' with
    | add u v hu hv =>
      rw [Polynomial.eval₂_add, map_add, Polynomial.eval_add, hu, hv]
    | monomial m c =>
      simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial]

/- ## Part 3: Cauchy root bound and continuous simple roots of `Q : Polynomial (Polynomial ℝ)` -/

lemma cauchy_root_bound (p : Polynomial ℝ) (hp : p ≠ 0) (y : ℝ) (hy : p.eval y = 0) :
    |y| ≤ 1 + (∑ k ∈ Finset.range p.natDegree, |p.coeff k|) / |p.leadingCoeff| := by
  have hlc : 0 < |p.leadingCoeff| := abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hsum_nn : 0 ≤ ∑ k ∈ Finset.range p.natDegree, |p.coeff k| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hy1 : |y| ≤ 1
  · linarith [div_nonneg hsum_nn hlc.le]
  · push Not at hy1
    have hd : 0 < p.natDegree := by
      by_contra hd0
      have hd' : p.natDegree = 0 := by omega
      have hconst := Polynomial.eq_C_of_natDegree_eq_zero hd'
      rw [hconst, Polynomial.eval_C] at hy
      have : p.coeff 0 ≠ 0 := by
        simpa [Polynomial.leadingCoeff, hd'] using Polynomial.leadingCoeff_ne_zero.mpr hp
      exact this hy
    have hsplit : p.eval y = p.leadingCoeff * y ^ p.natDegree +
        ∑ k ∈ Finset.range p.natDegree, p.coeff k * y ^ k := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_comm, Polynomial.leadingCoeff]
    have heq : p.leadingCoeff * y ^ p.natDegree =
        -(∑ k ∈ Finset.range p.natDegree, p.coeff k * y ^ k) := by linarith
    have h1 : |p.leadingCoeff| * |y| ^ p.natDegree ≤
        (∑ k ∈ Finset.range p.natDegree, |p.coeff k|) * |y| ^ (p.natDegree - 1) := by
      calc |p.leadingCoeff| * |y| ^ p.natDegree
          = |p.leadingCoeff * y ^ p.natDegree| := by rw [abs_mul, abs_pow]
        _ = |∑ k ∈ Finset.range p.natDegree, p.coeff k * y ^ k| := by rw [heq, abs_neg]
        _ ≤ ∑ k ∈ Finset.range p.natDegree, |p.coeff k * y ^ k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range p.natDegree, |p.coeff k| * |y| ^ k := by
            refine Finset.sum_congr rfl fun k _ => by rw [abs_mul, abs_pow]
        _ ≤ ∑ k ∈ Finset.range p.natDegree, |p.coeff k| * |y| ^ (p.natDegree - 1) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [Finset.mem_range] at hk
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1.le (by omega)) (abs_nonneg _)
        _ = (∑ k ∈ Finset.range p.natDegree, |p.coeff k|) * |y| ^ (p.natDegree - 1) :=
            (Finset.sum_mul _ _ _).symm
    have hpow : |y| ^ p.natDegree = |y| * |y| ^ (p.natDegree - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd]
    rw [hpow] at h1
    have hpos : 0 < |y| ^ (p.natDegree - 1) := pow_pos (by linarith) _
    have h2 : |p.leadingCoeff| * |y| ≤ ∑ k ∈ Finset.range p.natDegree, |p.coeff k| := by
      have : (|p.leadingCoeff| * |y|) * |y| ^ (p.natDegree - 1) ≤
          (∑ k ∈ Finset.range p.natDegree, |p.coeff k|) * |y| ^ (p.natDegree - 1) := by linarith
      exact le_of_mul_le_mul_right this hpos
    have h3 : |y| ≤ (∑ k ∈ Finset.range p.natDegree, |p.coeff k|) / |p.leadingCoeff| := by
      rw [le_div_iff₀ hlc]; linarith
    linarith

lemma eval_polyY_continuous (Q : Polynomial (Polynomial ℝ)) :
    Continuous (fun p : ℝ × ℝ => (Q.map (Polynomial.evalRingHom p.1)).eval p.2) := by
  have heq : (fun p : ℝ × ℝ => (Q.map (Polynomial.evalRingHom p.1)).eval p.2) =
      fun p => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then p.1 else p.2) (fromPolyY Q) := by
    funext p
    rw [eval_fromPolyY]
    rfl
  rw [heq]
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun i => by fin_cases i <;> [exact continuous_fst; exact continuous_snd])

lemma map_eval_natDegree (Q : Polynomial (Polynomial ℝ)) (x : ℝ)
    (hlc : Q.leadingCoeff.eval x ≠ 0) :
    (Q.map (Polynomial.evalRingHom x)).natDegree = Q.natDegree := by
  apply le_antisymm Polynomial.natDegree_map_le
  apply Polynomial.le_natDegree_of_ne_zero
  simpa [Polynomial.coeff_map] using hlc

lemma map_eval_ne_zero (Q : Polynomial (Polynomial ℝ)) (x : ℝ)
    (hlc : Q.leadingCoeff.eval x ≠ 0) :
    Q.map (Polynomial.evalRingHom x) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun p => p.coeff Q.natDegree) h0
  simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom, Polynomial.coeff_zero] at h1
  exact hlc h1

lemma map_eval_derivative (Q : Polynomial (Polynomial ℝ)) (x : ℝ) :
    (Q.map (Polynomial.evalRingHom x)).derivative =
      Q.derivative.map (Polynomial.evalRingHom x) :=
  Polynomial.derivative_map Q (Polynomial.evalRingHom x)

/-- Local root stability for a bivariate polynomial `Q(x, y)` at a point `x₀` where `Q(x₀, ·)` has
nonzero leading coefficient and only simple real roots. -/
lemma local_simple_roots (Q : Polynomial (Polynomial ℝ)) {U : Set ℝ} (hU : IsOpen U)
    {x₀ : ℝ} (hx₀ : x₀ ∈ U)
    (hlc : ∀ x ∈ U, Q.leadingCoeff.eval x ≠ 0)
    (hsimple : ∀ x ∈ U, ∀ y : ℝ, (Q.map (Polynomial.evalRingHom x)).eval y = 0 →
      (Q.map (Polynomial.evalRingHom x)).derivative.eval y ≠ 0) :
    ∀ ε₀ > (0 : ℝ), ∃ δ > 0, Set.Ioo (x₀ - δ) (x₀ + δ) ⊆ U ∧
      ∀ x ∈ Set.Ioo (x₀ - δ) (x₀ + δ),
        ∃ hcard : (Q.map (Polynomial.evalRingHom x)).roots.toFinset.card =
                  (Q.map (Polynomial.evalRingHom x₀)).roots.toFinset.card,
          ∀ k : Fin (Q.map (Polynomial.evalRingHom x₀)).roots.toFinset.card,
            |((Q.map (Polynomial.evalRingHom x)).roots.toFinset.orderEmbOfFin hcard k) -
             ((Q.map (Polynomial.evalRingHom x₀)).roots.toFinset.orderEmbOfFin rfl k)| < ε₀ := by
  classical
  intro ε₀ hε₀
  set Qx : ℝ → Polynomial ℝ := fun x => Q.map (Polynomial.evalRingHom x)
  set S₀ : Finset ℝ := (Qx x₀).roots.toFinset
  set s : ℕ := S₀.card
  set r : Fin s ↪o ℝ := S₀.orderEmbOfFin rfl
  -- Step 1: pick η > 0 so [x₀ - η, x₀ + η] ⊆ U.
  obtain ⟨η, hη_pos, hη_sub⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  let η' := η / 2
  have hη'_pos : 0 < η' := half_pos hη_pos
  have hIcc_sub : Set.Icc (x₀ - η') (x₀ + η') ⊆ U := by
    intro x hx
    apply hη_sub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hx1 : x₀ - η / 2 ≤ x := hx.1
    have hx2 : x ≤ x₀ + η / 2 := hx.2
    constructor <;> linarith [hη_pos]
  -- Step 2: uniform Cauchy root bound R on [x₀ - η', x₀ + η'].
  have hIcc_comp : IsCompact (Set.Icc (x₀ - η') (x₀ + η')) := isCompact_Icc
  have hIcc_ne : (Set.Icc (x₀ - η') (x₀ + η')).Nonempty := ⟨x₀, by linarith, by linarith⟩
  have hlc_cont : Continuous (fun x => |Q.leadingCoeff.eval x|) :=
    Q.leadingCoeff.continuous.abs
  obtain ⟨xmin, hxmin_mem, hxmin⟩ := hIcc_comp.exists_isMinOn hIcc_ne hlc_cont.continuousOn
  set cmin : ℝ := |Q.leadingCoeff.eval xmin|
  have hcmin_pos : 0 < cmin := abs_pos.mpr (hlc xmin (hIcc_sub hxmin_mem))
  have hsum_cont : Continuous (fun x => ∑ k ∈ Finset.range Q.natDegree, |(Q.coeff k).eval x|) :=
    continuous_finset_sum _ fun k _ => (Q.coeff k).continuous.abs
  obtain ⟨xmax, _, hxmax⟩ := hIcc_comp.exists_isMaxOn hIcc_ne hsum_cont.continuousOn
  set Mmax : ℝ := ∑ k ∈ Finset.range Q.natDegree, |(Q.coeff k).eval xmax|
  set R : ℝ := 2 + Mmax / cmin
  have hR_pos : 0 < R := by
    have : 0 ≤ Mmax := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have := div_nonneg this hcmin_pos.le
    linarith
  have hroot_bd : ∀ x ∈ Set.Icc (x₀ - η') (x₀ + η'), ∀ y : ℝ, (Qx x).eval y = 0 → |y| < R := by
    intro x hx y hy
    have hne : Qx x ≠ 0 := map_eval_ne_zero Q x (hlc x (hIcc_sub hx))
    have hdeg : (Qx x).natDegree = Q.natDegree := map_eval_natDegree Q x (hlc x (hIcc_sub hx))
    have hbd := cauchy_root_bound (Qx x) hne y hy
    rw [hdeg] at hbd
    have hlc_eq : (Qx x).leadingCoeff = Q.leadingCoeff.eval x := by
      rw [Polynomial.leadingCoeff, hdeg, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
        Polynomial.leadingCoeff]
    rw [hlc_eq] at hbd
    have hnum : ∑ k ∈ Finset.range Q.natDegree, |(Qx x).coeff k| ≤ Mmax := by
      have : ∀ k, (Qx x).coeff k = (Q.coeff k).eval x := fun k => by
        simp [Qx, Polynomial.coeff_map]
      simp_rw [this]
      exact hxmax hx
    have hden : cmin ≤ |Q.leadingCoeff.eval x| := hxmin hx
    have hdiv : (∑ k ∈ Finset.range Q.natDegree, |(Qx x).coeff k|) / |Q.leadingCoeff.eval x| ≤
        Mmax / cmin :=
      div_le_div₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hnum hcmin_pos hden
    linarith
  -- Step 3: pick isolating radius ε < ε₀ around each root r k of Qx x₀.
  have hderiv_ne : ∀ k : Fin s, (Qx x₀).derivative.eval (r k) ≠ 0 := by
    intro k
    have hmem : r k ∈ (Qx x₀).roots.toFinset := Finset.orderEmbOfFin_mem S₀ rfl k
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (map_eval_ne_zero Q x₀ (hlc x₀ hx₀))] at hmem
    exact hsimple x₀ hx₀ (r k) hmem
  have hderiv_nbhd : ∀ k : Fin s, ∃ εk > (0 : ℝ),
      ∀ y ∈ Set.Icc (r k - εk) (r k + εk),
        0 < (Qx x₀).derivative.eval (r k) * (Qx x₀).derivative.eval y := by
    intro k
    have hcont : Continuous (fun y => (Qx x₀).derivative.eval (r k) * (Qx x₀).derivative.eval y) :=
      continuous_const.mul (Qx x₀).derivative.continuous
    have hpos : 0 < (Qx x₀).derivative.eval (r k) * (Qx x₀).derivative.eval (r k) :=
      mul_self_pos.mpr (hderiv_ne k)
    obtain ⟨εk, hεk, hball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
      ((Qx x₀).derivative.eval (r k) * (Qx x₀).derivative.eval (r k) / 2) (half_pos hpos)
    refine ⟨εk / 2, half_pos hεk, fun y hy => ?_⟩
    have hdist : dist y (r k) < εk := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
    have hlt := hball hdist
    rw [Real.dist_eq, abs_lt] at hlt
    linarith
  choose εk hεk_pos hεk_sign using hderiv_nbhd
  have hroot_lt_R : ∀ k : Fin s, |r k| < R := by
    intro k
    have hmem : r k ∈ (Qx x₀).roots.toFinset := Finset.orderEmbOfFin_mem S₀ rfl k
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (map_eval_ne_zero Q x₀ (hlc x₀ hx₀))] at hmem
    exact hroot_bd x₀ ⟨by linarith, by linarith⟩ (r k) hmem
  -- Combine all upper bounds on ε into a single positive ε.
  let bd_set : Finset ℝ :=
    {ε₀} ∪ (Finset.univ.image εk) ∪ (Finset.univ.image fun k => (R - |r k|) / 2) ∪
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin s × Fin s => p.1 < p.2)).image
        (fun p => (r p.2 - r p.1) / 3)
  have hbd_ne : bd_set.Nonempty := ⟨ε₀, by simp [bd_set]⟩
  let ε : ℝ := bd_set.inf' hbd_ne id / 2
  have hbd_pos : ∀ z ∈ bd_set, 0 < z := by
    intro z hz
    simp only [bd_set, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_product] at hz
    rcases hz with (((rfl | ⟨k, rfl⟩) | ⟨k, rfl⟩) | ⟨⟨k₁, k₂⟩, hlt, rfl⟩)
    · exact hε₀
    · exact hεk_pos k
    · linarith [hroot_lt_R k]
    · have : r k₁ < r k₂ := r.strictMono hlt
      linarith
  have hε_pos : 0 < ε := by
    apply half_pos
    rw [Finset.lt_inf'_iff]
    exact hbd_pos
  have hε_lt : ∀ z ∈ bd_set, ε < z := by
    intro z hz
    have hle : bd_set.inf' hbd_ne id ≤ z := Finset.inf'_le id hz
    have hpos := hbd_pos z hz
    change bd_set.inf' hbd_ne id / 2 < z
    linarith
  have hε_lt_ε₀ : ε < ε₀ := hε_lt ε₀ (by simp [bd_set])
  have hε_lt_εk : ∀ k, ε < εk k := fun k => hε_lt (εk k) (by simp [bd_set])
  have hε_in_R : ∀ k, r k - ε ≥ -R ∧ r k + ε ≤ R := by
    intro k
    have hlt := hε_lt ((R - |r k|) / 2) (by simp [bd_set])
    have hab := abs_le.mp (le_of_lt (hroot_lt_R k))
    rcases le_total 0 (r k) with hr | hr
    · rw [abs_of_nonneg hr] at hlt; constructor <;> linarith
    · rw [abs_of_nonpos hr] at hlt; constructor <;> linarith
  have hε_disj : ∀ k₁ k₂ : Fin s, k₁ < k₂ → r k₁ + ε < r k₂ - ε := by
    intro k₁ k₂ hlt
    have h := hε_lt ((r k₂ - r k₁) / 3) (by
      simp only [bd_set, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_product, Finset.mem_univ, true_and]
      right; exact ⟨(k₁, k₂), hlt, rfl⟩)
    linarith
  -- Step 4: Positive lower bounds on |Qx x₀| on K, on |Qx' x₀| on ⋃ I_k, and on |Qx x₀ (r k ± ε)|.
  let K : Set ℝ := Set.Icc (-R) R \ ⋃ k : Fin s, Set.Ioo (r k - ε) (r k + ε)
  have hK_comp : IsCompact K :=
    isCompact_Icc.diff (isOpen_iUnion fun _ => isOpen_Ioo)
  have hK_nz : ∀ y ∈ K, (Qx x₀).eval y ≠ 0 := by
    intro y hy h0
    have hmem : y ∈ S₀ := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (map_eval_ne_zero Q x₀ (hlc x₀ hx₀))]
      exact h0
    have hrange : y ∈ Set.range r := by
      rw [Finset.range_orderEmbOfFin]
      exact hmem
    obtain ⟨k, rfl⟩ := hrange
    exact hy.2 (Set.mem_iUnion.mpr ⟨k, by linarith, by linarith⟩)
  have hmK_ex : ∃ mK > (0 : ℝ), ∀ y ∈ K, mK ≤ |(Qx x₀).eval y| := by
    by_cases hKne : K.Nonempty
    · obtain ⟨y0, hy0, hmin⟩ := hK_comp.exists_isMinOn hKne (Qx x₀).continuous.abs.continuousOn
      exact ⟨|(Qx x₀).eval y0|, abs_pos.mpr (hK_nz y0 hy0), fun y hy => hmin hy⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hKne
      exact ⟨1, zero_lt_one, fun y hy => by rw [hKne] at hy; exact False.elim hy⟩
  obtain ⟨mK, hmK_pos, hmK⟩ := hmK_ex
  have hIk_mono : ∀ k : Fin s, ∃ md > (0 : ℝ),
      ∀ y ∈ Set.Icc (r k - ε) (r k + ε),
        md ≤ |(Qx x₀).derivative.eval y| := by
    intro k
    have hne : (Set.Icc (r k - ε) (r k + ε)).Nonempty := ⟨r k, by linarith, by linarith⟩
    obtain ⟨y0, hy0, hmin⟩ := isCompact_Icc.exists_isMinOn hne
      (Qx x₀).derivative.continuous.abs.continuousOn
    have hnz : (Qx x₀).derivative.eval y0 ≠ 0 := by
      have hpos := hεk_sign k y0 ⟨by linarith [hy0.1, hε_lt_εk k], by linarith [hy0.2, hε_lt_εk k]⟩
      intro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl 0 hpos
    exact ⟨|(Qx x₀).derivative.eval y0|, abs_pos.mpr hnz, fun y hy => hmin hy⟩
  choose md hmd_pos hmd using hIk_mono
  have hmd_min_ex : ∃ mD > (0 : ℝ), ∀ k : Fin s, ∀ y ∈ Set.Icc (r k - ε) (r k + ε),
      mD ≤ |(Qx x₀).derivative.eval y| := by
    by_cases hs0 : Nonempty (Fin s)
    · obtain ⟨k0, _, hk0⟩ := Finset.exists_min_image Finset.univ md Finset.univ_nonempty
      exact ⟨md k0, hmd_pos k0, fun k y hy => (hk0 k (Finset.mem_univ k)).trans (hmd k y hy)⟩
    · exact ⟨1, zero_lt_one, fun k => False.elim (hs0 ⟨k⟩)⟩
  obtain ⟨mD, hmD_pos, hmD⟩ := hmd_min_ex
  -- Step 5: Uniform continuity of (x, y) ↦ (Qx x).eval y and (Qx x).derivative.eval y on box.
  let Box : Set (ℝ × ℝ) := Set.Icc (x₀ - η') (x₀ + η') ×ˢ Set.Icc (-R) R
  have hBox_comp : IsCompact Box := isCompact_Icc.prod isCompact_Icc
  have huc1 := hBox_comp.uniformContinuousOn_of_continuous (eval_polyY_continuous Q).continuousOn
  have huc2 := hBox_comp.uniformContinuousOn_of_continuous
    (eval_polyY_continuous Q.derivative).continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc1 huc2
  obtain ⟨δ1, hδ1_pos, hδ1⟩ := huc1 (mK / 2) (half_pos hmK_pos)
  obtain ⟨δ2, hδ2_pos, hδ2⟩ := huc2 (mD / 2) (half_pos hmD_pos)
  set δ := min η' (min δ1 δ2)
  have hδ_pos : 0 < δ := lt_min hη'_pos (lt_min hδ1_pos hδ2_pos)
  refine ⟨δ, hδ_pos, ?_, ?_⟩
  · intro x hx
    exact hIcc_sub ⟨by linarith [hx.1, min_le_left η' (min δ1 δ2)],
      by linarith [hx.2, min_le_left η' (min δ1 δ2)]⟩
  · intro x hx
    have hx_Icc : x ∈ Set.Icc (x₀ - η') (x₀ + η') :=
      ⟨by linarith [hx.1, min_le_left η' (min δ1 δ2)],
       by linarith [hx.2, min_le_left η' (min δ1 δ2)]⟩
    have hx_dist1 : dist x x₀ < δ1 := by
      rw [Real.dist_eq, abs_lt]
      have hle : δ ≤ δ1 := (min_le_right _ _).trans (min_le_left _ _)
      constructor <;> linarith [hx.1, hx.2]
    have hx_dist2 : dist x x₀ < δ2 := by
      rw [Real.dist_eq, abs_lt]
      have hle : δ ≤ δ2 := (min_le_right _ _).trans (min_le_right _ _)
      constructor <;> linarith [hx.1, hx.2]
    have hclose1 : ∀ y ∈ Set.Icc (-R) R, |(Qx x).eval y - (Qx x₀).eval y| < mK / 2 := by
      intro y hy
      have h := hδ1 (x, y) ⟨hx_Icc, hy⟩ (x₀, y) ⟨⟨by linarith, by linarith⟩, hy⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hx_dist1)
      simpa [Real.dist_eq, Qx] using h
    have hclose2 : ∀ y ∈ Set.Icc (-R) R,
        |(Qx x).derivative.eval y - (Qx x₀).derivative.eval y| < mD / 2 := by
      intro y hy
      have h := hδ2 (x, y) ⟨hx_Icc, hy⟩ (x₀, y) ⟨⟨by linarith, by linarith⟩, hy⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hx_dist2)
      simpa [Real.dist_eq, Qx, map_eval_derivative] using h
    -- No roots in K
    have hnoK : ∀ y ∈ K, (Qx x).eval y ≠ 0 := by
      intro y hy h0
      have hc := hclose1 y hy.1
      have hm := hmK y hy
      rw [h0, zero_sub, abs_neg] at hc
      linarith
    -- On each [r k - ε, r k + ε], Qx x has a unique root y_k, and it lies in (r k - ε, r k + ε).
    have hex_uniq : ∀ k : Fin s, ∃! y, y ∈ Set.Ioo (r k - ε) (r k + ε) ∧ (Qx x).eval y = 0 := by
      intro k
      have hIk_sub : Set.Icc (r k - ε) (r k + ε) ⊆ Set.Icc (-R) R :=
        fun y hy => ⟨(hε_in_R k).1.trans hy.1, hy.2.trans (hε_in_R k).2⟩
      have hend_K : r k - ε ∈ K ∧ r k + ε ∈ K := by
        constructor
        · refine ⟨hIk_sub ⟨le_rfl, by linarith⟩, ?_⟩
          simp only [Set.mem_iUnion, Set.mem_Ioo, not_exists, not_and, not_lt]
          intro k' hk'
          by_cases hlt : k' < k
          · linarith [hε_disj k' k hlt]
          · rcases eq_or_lt_of_le (not_lt.mp hlt) with rfl | hgt
            · linarith
            · linarith [hε_disj k k' hgt]
        · refine ⟨hIk_sub ⟨by linarith, le_rfl⟩, ?_⟩
          simp only [Set.mem_iUnion, Set.mem_Ioo, not_exists, not_and, not_lt]
          intro k' hk'
          by_cases hlt : k' < k
          · linarith [hε_disj k' k hlt]
          · rcases eq_or_lt_of_le (not_lt.mp hlt) with rfl | hgt
            · linarith
            · linarith [hε_disj k k' hgt]
      have hderiv_sign : ∀ y ∈ Set.Icc (r k - ε) (r k + ε),
          0 < (Qx x₀).derivative.eval (r k) * (Qx x).derivative.eval y := by
        intro y hy
        have hpos0 := hεk_sign k y ⟨by linarith [hy.1, hε_lt_εk k], by linarith [hy.2, hε_lt_εk k]⟩
        have hmdy := hmD k y hy
        have hc2 := hclose2 y (hIk_sub hy)
        have hsame : 0 < (Qx x₀).derivative.eval y * (Qx x).derivative.eval y := by
          rcases lt_or_gt_of_ne (show (Qx x₀).derivative.eval y ≠ 0 by
            intro h0; rw [h0, mul_zero] at hpos0; exact lt_irrefl 0 hpos0) with hneg | hpos
          · rw [abs_of_neg hneg] at hmdy
            have hlt' := (abs_lt.mp hc2).2
            have : (Qx x).derivative.eval y < 0 := by linarith
            exact mul_pos_of_neg_of_neg hneg this
          · rw [abs_of_pos hpos] at hmdy
            have hgt' := (abs_lt.mp hc2).1
            have : 0 < (Qx x).derivative.eval y := by linarith
            exact mul_pos hpos this
        have hsq : 0 < ((Qx x₀).derivative.eval y) ^ 2 := sq_pos_of_ne_zero (by
          intro h0; rw [h0, mul_zero] at hpos0; exact lt_irrefl 0 hpos0)
        have hprod : 0 < ((Qx x₀).derivative.eval (r k) * (Qx x).derivative.eval y) *
            ((Qx x₀).derivative.eval y) ^ 2 := by
          have : ((Qx x₀).derivative.eval (r k) * (Qx x).derivative.eval y) *
              ((Qx x₀).derivative.eval y) ^ 2 =
              ((Qx x₀).derivative.eval (r k) * (Qx x₀).derivative.eval y) *
              ((Qx x₀).derivative.eval y * (Qx x).derivative.eval y) := by ring
          rw [this]
          exact mul_pos hpos0 hsame
        exact pos_of_mul_pos_left hprod hsq.le
      -- Strict monotonicity of Qx x₀ and Qx x on [r k - ε, r k + ε]
      have hroot0 : (Qx x₀).eval (r k) = 0 := by
        have hmem : r k ∈ S₀ := Finset.orderEmbOfFin_mem S₀ rfl k
        rwa [Multiset.mem_toFinset, Polynomial.mem_roots (map_eval_ne_zero Q x₀ (hlc x₀ hx₀))] at hmem
      have hmono : ∀ (z : ℝ) (hsign : ∀ y ∈ Set.Icc (r k - ε) (r k + ε),
          0 < (Qx x₀).derivative.eval (r k) * (Qx z).derivative.eval y),
          StrictMonoOn (fun y => (Qx x₀).derivative.eval (r k) * (Qx z).eval y)
            (Set.Icc (r k - ε) (r k + ε)) := by
        intro z hsign
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        · exact (continuous_const.mul (Qx z).continuous).continuousOn
        · intro y hy
          have hhd : HasDerivAt (fun t => (Qx x₀).derivative.eval (r k) * (Qx z).eval t)
              ((Qx x₀).derivative.eval (r k) * (Qx z).derivative.eval y) y :=
            (Polynomial.hasDerivAt (Qx z) y).const_mul _
          rw [hhd.deriv]
          exact hsign y (interior_subset hy)
      have hmono0 := hmono x₀ (fun y hy =>
        hεk_sign k y ⟨by linarith [hy.1, hε_lt_εk k], by linarith [hy.2, hε_lt_εk k]⟩)
      have hmonox := hmono x hderiv_sign
      -- Opposite signs of Qx x₀ at endpoints, hence also for Qx x!
      have hL0 : (Qx x₀).derivative.eval (r k) * (Qx x₀).eval (r k - ε) < 0 := by
        have := hmono0 (a := r k - ε) (b := r k) ⟨le_rfl, by linarith [hε_pos]⟩
          ⟨by linarith [hε_pos], by linarith [hε_pos]⟩ (by linarith [hε_pos])
        simpa [hroot0] using this
      have hR0 : 0 < (Qx x₀).derivative.eval (r k) * (Qx x₀).eval (r k + ε) := by
        have := hmono0 (a := r k) (b := r k + ε) ⟨by linarith [hε_pos], by linarith [hε_pos]⟩
          ⟨by linarith [hε_pos], le_rfl⟩ (by linarith [hε_pos])
        simpa [hroot0] using this
      have hsame_end : ∀ y ∈ K, 0 < (Qx x₀).eval y * (Qx x).eval y := by
        intro y hy
        have hm := hmK y hy
        have hc := hclose1 y hy.1
        rcases lt_or_gt_of_ne (hK_nz y hy) with hneg | hpos
        · rw [abs_of_neg hneg] at hm
          have : (Qx x).eval y < 0 := by linarith [(abs_lt.mp hc).2]
          exact mul_pos_of_neg_of_neg hneg this
        · rw [abs_of_pos hpos] at hm
          have : 0 < (Qx x).eval y := by linarith [(abs_lt.mp hc).1]
          exact mul_pos hpos this
      have hLx : (Qx x₀).derivative.eval (r k) * (Qx x).eval (r k - ε) < 0 := by
        have hs1 := hsame_end (r k - ε) hend_K.1
        have hsq : 0 < ((Qx x₀).eval (r k - ε)) ^ 2 := sq_pos_of_ne_zero (hK_nz _ hend_K.1)
        have : ((Qx x₀).derivative.eval (r k) * (Qx x).eval (r k - ε)) *
            ((Qx x₀).eval (r k - ε)) ^ 2 < 0 := by
          have heq : ((Qx x₀).derivative.eval (r k) * (Qx x).eval (r k - ε)) *
              ((Qx x₀).eval (r k - ε)) ^ 2 =
              ((Qx x₀).derivative.eval (r k) * (Qx x₀).eval (r k - ε)) *
              ((Qx x₀).eval (r k - ε) * (Qx x).eval (r k - ε)) := by ring
          rw [heq]; exact mul_neg_of_neg_of_pos hL0 hs1
        exact neg_of_mul_neg_left this hsq.le
      have hRx : 0 < (Qx x₀).derivative.eval (r k) * (Qx x).eval (r k + ε) := by
        have hs1 := hsame_end (r k + ε) hend_K.2
        have hsq : 0 < ((Qx x₀).eval (r k + ε)) ^ 2 := sq_pos_of_ne_zero (hK_nz _ hend_K.2)
        have : 0 < ((Qx x₀).derivative.eval (r k) * (Qx x).eval (r k + ε)) *
            ((Qx x₀).eval (r k + ε)) ^ 2 := by
          have heq : ((Qx x₀).derivative.eval (r k) * (Qx x).eval (r k + ε)) *
              ((Qx x₀).eval (r k + ε)) ^ 2 =
              ((Qx x₀).derivative.eval (r k) * (Qx x₀).eval (r k + ε)) *
              ((Qx x₀).eval (r k + ε) * (Qx x).eval (r k + ε)) := by ring
          rw [heq]; exact mul_pos hR0 hs1
        exact pos_of_mul_pos_left this hsq.le
      -- Existence by IVT
      obtain ⟨y, hy_Icc, hy_zero⟩ := intermediate_value_Icc (by linarith : r k - ε ≤ r k + ε)
        (continuous_const.mul (Qx x).continuous).continuousOn ⟨hLx.le, hRx.le⟩
      have hy_ev0 : (Qx x).eval y = 0 := by
        rcases mul_eq_zero.mp hy_zero with h1 | h2
        · exact False.elim (hderiv_ne k h1)
        · exact h2
      have hy_Ioo : y ∈ Set.Ioo (r k - ε) (r k + ε) := by
        refine ⟨lt_of_le_of_ne hy_Icc.1 ?_, lt_of_le_of_ne hy_Icc.2 ?_⟩
        · intro h; subst h; exact hnoK (r k - ε) hend_K.1 hy_ev0
        · intro h; subst h; exact hnoK (r k + ε) hend_K.2 hy_ev0
      refine ⟨y, ⟨hy_Ioo, hy_ev0⟩, ?_⟩
      intro y' ⟨hy'_Ioo, hy'_ev0⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hmonox ⟨hy'_Ioo.1.le, hy'_Ioo.2.le⟩ ⟨hy_Ioo.1.le, hy_Ioo.2.le⟩ hlt
        simp [hy_ev0, hy'_ev0] at this
      · have := hmonox ⟨hy_Ioo.1.le, hy_Ioo.2.le⟩ ⟨hy'_Ioo.1.le, hy'_Ioo.2.le⟩ hgt
        simp [hy_ev0, hy'_ev0] at this
    -- Assemble the bijection Fin s ↪o (Qx x).roots.toFinset
    choose yk hyk_spec hyk_uniq using hex_uniq
    have hyk_mono : StrictMono yk := by
      intro k₁ k₂ hlt
      have h1 := (hyk_spec k₁).1.2
      have h2 := (hyk_spec k₂).1.1
      have h3 := hε_disj k₁ k₂ hlt
      linarith
    have hyk_mem : ∀ k : Fin s, yk k ∈ (Qx x).roots.toFinset := by
      intro k
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (map_eval_ne_zero Q x (hlc x (hIcc_sub hx_Icc)))]
      exact (hyk_spec k).2
    have hroots_eq : (Qx x).roots.toFinset = Finset.univ.image yk := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hy
        rw [Multiset.mem_toFinset,
          Polynomial.mem_roots (map_eval_ne_zero Q x (hlc x (hIcc_sub hx_Icc)))] at hy
        have hy_bd : y ∈ Set.Icc (-R) R := abs_le.mp (hroot_bd x hx_Icc y hy).le
        have hy_nK : y ∉ K := fun hK => hnoK y hK hy
        have hy_in : y ∈ ⋃ k : Fin s, Set.Ioo (r k - ε) (r k + ε) := by
          by_contra hnot; exact hy_nK ⟨hy_bd, hnot⟩
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy_in
        exact ⟨k, (hyk_uniq k y ⟨hk, hy⟩).symm⟩
      · rintro ⟨k, rfl⟩
        exact hyk_mem k
    have hcard : (Qx x).roots.toFinset.card = s := by
      rw [hroots_eq, Finset.card_image_of_injective _ hyk_mono.injective, Finset.card_fin]
    refine ⟨hcard, fun k => ?_⟩
    -- Show orderEmbOfFin equals yk!
    have hemb_eq : ∀ j : Fin s, (Qx x).roots.toFinset.orderEmbOfFin hcard j = yk j := by
      have hfeq := Finset.orderEmbOfFin_unique hcard
        (f := yk) (fun j => hyk_mem j) hyk_mono
      intro j
      exact (congrArg (fun f => f j) hfeq).symm
    rw [hemb_eq k]
    have h1 := (hyk_spec k).1
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, hε_lt_ε₀]

/- ## Part 4: Connected root branches and 2D polynomial projection via `RatFunc ℝ` -/

lemma connected_simple_roots (Q : Polynomial (Polynomial ℝ)) {U : Set ℝ}
    (hU_open : IsOpen U) (hU_conn : IsConnected U)
    (hlc : ∀ x ∈ U, Q.leadingCoeff.eval x ≠ 0)
    (hsimple : ∀ x ∈ U, ∀ y : ℝ, (Q.map (Polynomial.evalRingHom x)).eval y = 0 →
      (Q.map (Polynomial.evalRingHom x)).derivative.eval y ≠ 0) :
    ∃ (s : ℕ) (ξ : Fin s → ℝ → ℝ),
      (∀ x ∈ U, StrictMono (fun k => ξ k x)) ∧
      (∀ k : Fin s, ContinuousOn (ξ k) U) ∧
      (∀ x ∈ U, ∀ y : ℝ,
        (Q.map (Polynomial.evalRingHom x)).eval y = 0 ↔ ∃ k : Fin s, y = ξ k x) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hU_conn.nonempty
  set Qx : ℝ → Polynomial ℝ := fun x => Q.map (Polynomial.evalRingHom x)
  set s : ℕ := (Qx x₀).roots.toFinset.card
  -- Step 1: root count is constant on connected U.
  have hcard_const : ∀ x ∈ U, (Qx x).roots.toFinset.card = s := by
    let A : Set ℝ := {x | (Qx x).roots.toFinset.card = s}
    let B : Set ℝ := {x | (Qx x).roots.toFinset.card ≠ s}
    have hA_open : IsOpen (U ∩ A) := by
      rw [Metric.isOpen_iff]
      intro x ⟨hxU, hxA⟩
      obtain ⟨δ, hδ_pos, hδ_sub, hδ_eq⟩ := local_simple_roots Q hU_open hxU hlc hsimple 1 zero_lt_one
      refine ⟨δ, hδ_pos, fun y hy => ?_⟩
      have hyIoo : y ∈ Set.Ioo (x - δ) (x + δ) := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
        exact ⟨by linarith, by linarith⟩
      obtain ⟨hc, _⟩ := hδ_eq y hyIoo
      exact ⟨hδ_sub hyIoo, hc.trans hxA⟩
    have hB_open : IsOpen (U ∩ B) := by
      rw [Metric.isOpen_iff]
      intro x ⟨hxU, hxB⟩
      obtain ⟨δ, hδ_pos, hδ_sub, hδ_eq⟩ := local_simple_roots Q hU_open hxU hlc hsimple 1 zero_lt_one
      refine ⟨δ, hδ_pos, fun y hy => ?_⟩
      have hyIoo : y ∈ Set.Ioo (x - δ) (x + δ) := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
        exact ⟨by linarith, by linarith⟩
      obtain ⟨hc, _⟩ := hδ_eq y hyIoo
      exact ⟨hδ_sub hyIoo, fun h => hxB (hc.symm.trans h)⟩
    have hcov : U ⊆ (U ∩ A) ∪ (U ∩ B) := by
      intro x hx
      by_cases h : (Qx x).roots.toFinset.card = s
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    have hdisj : (U ∩ ((U ∩ A) ∩ (U ∩ B))).Nonempty → False := by
      rintro ⟨x, _, ⟨_, h1⟩, ⟨_, h2⟩⟩; exact h2 h1
    have hneA : (U ∩ (U ∩ A)).Nonempty := ⟨x₀, hx₀, hx₀, rfl⟩
    intro x hx
    by_contra hne
    have hneB : (U ∩ (U ∩ B)).Nonempty := ⟨x, hx, hx, hne⟩
    exact hdisj (hU_conn.isPreconnected (U ∩ A) (U ∩ B) hA_open hB_open hcov hneA hneB)
  -- Step 2: define ξ k x using orderEmbOfFin.
  let ξ : Fin s → ℝ → ℝ := fun k x =>
    if h : (Qx x).roots.toFinset.card = s then (Qx x).roots.toFinset.orderEmbOfFin h k else 0
  refine ⟨s, ξ, ?_, ?_, ?_⟩
  · intro x hx
    have hc := hcard_const x hx
    have heq : (fun k => ξ k x) = fun k => (Qx x).roots.toFinset.orderEmbOfFin hc k := by
      funext k; simp [ξ, hc]
    rw [heq]
    exact ((Qx x).roots.toFinset.orderEmbOfFin hc).strictMono
  · intro k
    rw [Metric.continuousOn_iff]
    intro x hx ε hε
    obtain ⟨δ, hδ_pos, _, hδ_eq⟩ := local_simple_roots Q hU_open hx hlc hsimple ε hε
    refine ⟨δ, hδ_pos, fun y hyU hyd => ?_⟩
    have hyIoo : y ∈ Set.Ioo (x - δ) (x + δ) := by
      rw [Real.dist_eq, abs_lt] at hyd
      exact ⟨by linarith, by linarith⟩
    obtain ⟨hc_xy, hclose⟩ := hδ_eq y hyIoo
    have hcx : (Qx x).roots.toFinset.card = s := hcard_const x hx
    have hcy : (Qx y).roots.toFinset.card = s := hcard_const y hyU
    have h1 : ξ k y = (Qx y).roots.toFinset.orderEmbOfFin hcy k := by simp [ξ, hcy]
    have h2 : ξ k x = (Qx x).roots.toFinset.orderEmbOfFin hcx k := by simp [ξ, hcx]
    rw [Real.dist_eq, h1, h2]
    have hstep : ∀ {n : ℕ} (hn : (Qx x).roots.toFinset.card = n)
        (hcy' : (Qx y).roots.toFinset.card = n) (k : Fin n),
        |(Qx y).roots.toFinset.orderEmbOfFin hcy' k -
         (Qx x).roots.toFinset.orderEmbOfFin hn k| < ε := by
      intro n hn
      subst hn
      intro hcy' k'
      exact hclose k'
    exact hstep hcx hcy k
  · intro x hx y
    have hc := hcard_const x hx
    have hne : Qx x ≠ 0 := map_eval_ne_zero Q x (hlc x hx)
    change (Qx x).IsRoot y ↔ ∃ k, y = ξ k x
    rw [← Polynomial.mem_roots hne, ← Multiset.mem_toFinset]
    constructor
    · intro hy
      have hrange : y ∈ Set.range ((Qx x).roots.toFinset.orderEmbOfFin hc) := by
        rw [Finset.range_orderEmbOfFin]; exact hy
      obtain ⟨k, rfl⟩ := hrange
      exact ⟨k, by simp [ξ, hc]⟩
    · rintro ⟨k, rfl⟩
      simp only [ξ, hc, ↓reduceDIte]
      exact Finset.orderEmbOfFin_mem _ hc k

lemma exists_clear_denom (p : Polynomial (RatFunc ℝ)) :
    ∃ (D : Polynomial ℝ) (q : Polynomial (Polynomial ℝ)),
      D ≠ 0 ∧
      Polynomial.C (algebraMap (Polynomial ℝ) (RatFunc ℝ) D) * p =
        q.map (algebraMap (Polynomial ℝ) (RatFunc ℝ)) := by
  classical
  let emb : Polynomial ℝ →+* RatFunc ℝ := algebraMap (Polynomial ℝ) (RatFunc ℝ)
  have hcoeff : ∀ k : ℕ, ∃ (n d : Polynomial ℝ), d ≠ 0 ∧ p.coeff k * emb d = emb n := by
    intro k
    obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := Polynomial ℝ) (p.coeff k)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨n, d, hd0, ?_⟩
    rw [← hnd, div_mul_cancel₀ _ (by exact (map_ne_zero_iff emb (IsFractionRing.injective _ _)).mpr hd0)]
  choose num den hden_ne hden_eq using hcoeff
  let D : Polynomial ℝ := ∏ k ∈ Finset.range (p.natDegree + 1), den k
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hden_ne k
  let q : Polynomial (Polynomial ℝ) :=
    ∑ k ∈ Finset.range (p.natDegree + 1),
      Polynomial.monomial k (num k * ∏ j ∈ (Finset.range (p.natDegree + 1)).erase k, den j)
  refine ⟨D, q, hD_ne, ?_⟩
  ext k
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, q, Finset.sum_apply,
    Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  by_cases hk : k ∈ Finset.range (p.natDegree + 1)
  · rw [Finset.sum_eq_single k]
    · simp only [↓reduceIte, map_mul, map_prod]
      have hD_split : D = den k * ∏ j ∈ (Finset.range (p.natDegree + 1)).erase k, den j :=
        (Finset.mul_prod_erase _ _ hk).symm
      rw [hD_split, map_mul, map_prod]
      calc emb (den k) * (∏ j ∈ (Finset.range (p.natDegree + 1)).erase k, emb (den j)) * p.coeff k
          = (p.coeff k * emb (den k)) *
              ∏ j ∈ (Finset.range (p.natDegree + 1)).erase k, emb (den j) := by ring
        _ = emb (num k) * ∏ j ∈ (Finset.range (p.natDegree + 1)).erase k, emb (den j) := by
              rw [hden_eq k]
    · intro b _ hbk; simp [hbk]
    · intro h; exact False.elim (h hk)
  · rw [Finset.sum_eq_zero]
    · rw [Finset.mem_range] at hk
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, map_zero]
    · intro b hb
      have hbk : b ≠ k := fun h => hk (h ▸ hb)
      simp [hbk]

lemma map_emb_injective :
    Function.Injective (Polynomial.map (algebraMap (Polynomial ℝ) (RatFunc ℝ))) :=
  Polynomial.map_injective _ (IsFractionRing.injective (Polynomial ℝ) (RatFunc ℝ))

lemma irr_coprime_or_dvd {K : Type*} [Field K] {r : Polynomial K} (hr : Irreducible r)
    (b : Polynomial K) : IsCoprime r b ∨ r ∣ b := by
  classical
  let g := EuclideanDomain.gcd r b
  have hg_dvd_r : g ∣ r := EuclideanDomain.gcd_dvd_left r b
  have hg_dvd_b : g ∣ b := EuclideanDomain.gcd_dvd_right r b
  obtain ⟨c, hc⟩ := hg_dvd_r
  rcases hr.isUnit_or_isUnit hc with hgu | hcu
  · left
    obtain ⟨u, hu⟩ := hgu.exists_right_inv
    refine ⟨u * EuclideanDomain.gcdA r b, u * EuclideanDomain.gcdB r b, ?_⟩
    calc u * EuclideanDomain.gcdA r b * r + u * EuclideanDomain.gcdB r b * b
        = u * (r * EuclideanDomain.gcdA r b + b * EuclideanDomain.gcdB r b) := by ring
      _ = u * g := by rw [← EuclideanDomain.gcd_eq_gcd_ab]
      _ = 1 := by rw [mul_comm, hu]
  · right
    have hr_dvd_g : r ∣ g := by
      obtain ⟨v, hv⟩ := hcu.exists_right_inv
      exact ⟨v, by rw [hc, mul_assoc, hv, mul_one]⟩
    exact hr_dvd_g.trans hg_dvd_b

lemma ratfunc_sqfree_part (B : Finset (Polynomial (Polynomial ℝ)))
    (hB : ∀ a ∈ B, a ≠ 0) :
    ∃ (Q : Polynomial (Polynomial ℝ)) (Crit : Finset ℝ),
      Q ≠ 0 ∧
      (∀ x : ℝ, x ∉ Crit → Q.leadingCoeff.eval x ≠ 0) ∧
      (∀ x : ℝ, x ∉ Crit → ∀ y : ℝ,
        (Q.map (Polynomial.evalRingHom x)).eval y = 0 →
        (Q.map (Polynomial.evalRingHom x)).derivative.eval y ≠ 0) ∧
      (∀ a ∈ B, ∀ x : ℝ, x ∉ Crit → ∀ y : ℝ,
        (a.map (Polynomial.evalRingHom x)).eval y = 0 →
        (Q.map (Polynomial.evalRingHom x)).eval y = 0) ∧
      (∀ a ∈ B, ∃ R : Polynomial (Polynomial ℝ),
        ∀ x : ℝ, x ∉ Crit → ∀ y : ℝ,
          (Q.map (Polynomial.evalRingHom x)).eval y = 0 →
          ((a.map (Polynomial.evalRingHom x)).eval y = 0 ↔
           (R.map (Polynomial.evalRingHom x)).eval y ≠ 0)) := by
  classical
  let emb : Polynomial ℝ →+* RatFunc ℝ := algebraMap (Polynomial ℝ) (RatFunc ℝ)
  let P : Polynomial (Polynomial ℝ) := ∏ a ∈ B, a
  have hP_ne : P ≠ 0 := Finset.prod_ne_zero_iff.mpr hB
  let P_rat : Polynomial (RatFunc ℝ) := P.map emb
  have hP_rat_ne : P_rat ≠ 0 := by
    intro h0; exact hP_ne (map_emb_injective (by simpa [P_rat] using h0))
  let F : Finset (Polynomial (RatFunc ℝ)) :=
    (UniqueFactorizationMonoid.normalizedFactors P_rat).toFinset
  have hF_irr : ∀ r ∈ F, Irreducible r := fun r hr =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor r (Multiset.mem_toFinset.mp hr)
  have hF_norm : ∀ r ∈ F, normalize r = r := fun r hr =>
    UniqueFactorizationMonoid.normalize_normalized_factor r (Multiset.mem_toFinset.mp hr)
  let Q_rat : Polynomial (RatFunc ℝ) := ∏ r ∈ F, r
  have hQ_rat_ne : Q_rat ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r hr => (hF_irr r hr).ne_zero
  -- Q_rat is separable since it's a product of distinct normalized irreducibles in char 0.
  have hQ_sep : Q_rat.Separable := by
    have hsep_fin : ∀ (S : Finset (Polynomial (RatFunc ℝ))),
        (∀ r ∈ S, Irreducible r) → (∀ r ∈ S, normalize r = r) →
        (∏ r ∈ S, r).Separable := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _ _; simpa using Polynomial.separable_one
      | @insert r S hrS ih =>
        intro hI hN
        rw [Finset.prod_insert hrS]
        have hrI : Irreducible r := hI r (Finset.mem_insert_self r S)
        have hr_sep : r.Separable := hrI.separable
        have hS_sep : (∏ s ∈ S, s).Separable :=
          ih (fun s hs => hI s (Finset.mem_insert_of_mem hs))
             (fun s hs => hN s (Finset.mem_insert_of_mem hs))
        have hcop : IsCoprime r (∏ s ∈ S, s) := by
          apply IsCoprime.prod_right
          intro s hs
          have hsI : Irreducible s := hI s (Finset.mem_insert_of_mem hs)
          rcases irr_coprime_or_dvd hrI s with h | hdvd
          · exact h
          · have hassoc : Associated r s :=
              hrI.associated_of_dvd hsI hdvd
            have heq : r = s := by
              rw [← hN r (Finset.mem_insert_self r S), ← hN s (Finset.mem_insert_of_mem hs)]
              exact normalize_eq_normalize_iff.mpr ⟨hassoc.dvd, hassoc.symm.dvd⟩
            exact False.elim (hrS (heq ▸ hs))
        exact hr_sep.mul hS_sep hcop
    exact hsep_fin F hF_irr hF_norm
  -- Clear denominators of Q_rat to get Q ∈ ℝ[x][y]
  obtain ⟨DQ, Q, hDQ_ne, hQ_eq⟩ := exists_clear_denom Q_rat
  have hQ_ne : Q ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero] at hQ_eq
    have hDQ_rat : Polynomial.C (emb DQ) ≠ 0 := by
      simp [Polynomial.C_ne_zero, map_ne_zero_iff emb (IsFractionRing.injective _ _), hDQ_ne]
    exact (mul_ne_zero hDQ_rat hQ_rat_ne) hQ_eq
  -- Bezout for Q and Q.derivative
  obtain ⟨u_rat, v_rat, huv_rat⟩ := hQ_sep
  obtain ⟨Du, u, hDu_ne, hu_eq⟩ := exists_clear_denom u_rat
  obtain ⟨Dv, v, hDv_ne, hv_eq⟩ := exists_clear_denom v_rat
  have hbezQ : (Polynomial.C (DQ * Dv) * u) * Q + (Polynomial.C (DQ * Du) * v) * Q.derivative =
      Polynomial.C (DQ * DQ * Du * Dv) := by
    apply map_emb_injective
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    rw [← Polynomial.derivative_map, ← hQ_eq, Polynomial.derivative_C_mul]
    have hu' : Polynomial.map emb u = Polynomial.C (emb Du) * u_rat := hu_eq.symm
    have hv' : Polynomial.map emb v = Polynomial.C (emb Dv) * v_rat := hv_eq.symm
    rw [hu', hv']
    have h1 : Polynomial.C (emb (DQ * Dv)) * (Polynomial.C (emb Du) * u_rat) *
        (Polynomial.C (emb DQ) * Q_rat) +
        Polynomial.C (emb (DQ * Du)) * (Polynomial.C (emb Dv) * v_rat) *
        (Polynomial.C (emb DQ) * Q_rat.derivative) =
        Polynomial.C (emb (DQ * DQ * Du * Dv)) * (u_rat * Q_rat + v_rat * Q_rat.derivative) := by
      simp only [map_mul, Polynomial.C_mul]; ring
    rw [h1, huv_rat, mul_one]
  -- For each a ∈ B, split F into factors dividing a_rat and factors not dividing a_rat
  have hper_a : ∀ a ∈ B, ∃ (R : Polynomial (Polynomial ℝ)) (ca : Polynomial ℝ),
      ca ≠ 0 ∧
      (∀ x : ℝ, ca.eval x ≠ 0 → ∀ y : ℝ,
        (a.map (Polynomial.evalRingHom x)).eval y = 0 →
        (Q.map (Polynomial.evalRingHom x)).eval y = 0) ∧
      (∀ x : ℝ, ca.eval x ≠ 0 → ∀ y : ℝ,
        (Q.map (Polynomial.evalRingHom x)).eval y = 0 →
        ((a.map (Polynomial.evalRingHom x)).eval y = 0 ↔
         (R.map (Polynomial.evalRingHom x)).eval y ≠ 0)) := by
    intro a ha
    let a_rat : Polynomial (RatFunc ℝ) := a.map emb
    have ha_rat_ne : a_rat ≠ 0 := by
      intro h0; exact hB a ha (map_emb_injective (by simpa [a_rat] using h0))
    let Fa : Finset (Polynomial (RatFunc ℝ)) := F.filter fun r => r ∣ a_rat
    let Fna : Finset (Polynomial (RatFunc ℝ)) := F.filter fun r => ¬ r ∣ a_rat
    let Qa_rat : Polynomial (RatFunc ℝ) := ∏ r ∈ Fa, r
    let Ra_rat : Polynomial (RatFunc ℝ) := ∏ r ∈ Fna, r
    have hQ_split : Q_rat = Qa_rat * Ra_rat := by
      dsimp only [Q_rat, Qa_rat, Ra_rat]
      exact (Finset.prod_filter_mul_prod_filter_not F (fun r => r ∣ a_rat) id).symm
    -- Qa_rat ∣ a_rat (product of distinct normalized irreducibles dividing a_rat)
    have hQa_dvd_a : Qa_rat ∣ a_rat := by
      have hprod_dvd : ∀ (S : Finset (Polynomial (RatFunc ℝ))),
          (∀ r ∈ S, Irreducible r) → (∀ r ∈ S, normalize r = r) →
          (∀ r ∈ S, r ∣ a_rat) → (∏ r ∈ S, r) ∣ a_rat := by
        intro S
        induction S using Finset.induction_on with
        | empty => intro _ _ _; simp
        | @insert r S hrS ih =>
          intro hI hN hD
          rw [Finset.prod_insert hrS]
          have hcop : IsCoprime r (∏ s ∈ S, s) := by
            apply IsCoprime.prod_right
            intro s hs
            have hrI := hI r (Finset.mem_insert_self r S)
            have hsI := hI s (Finset.mem_insert_of_mem hs)
            rcases irr_coprime_or_dvd hrI s with h | hdvd
            · exact h
            · have heq : r = s := by
                rw [← hN r (Finset.mem_insert_self r S), ← hN s (Finset.mem_insert_of_mem hs)]
                have hassoc := hrI.associated_of_dvd hsI hdvd
                exact normalize_eq_normalize_iff.mpr ⟨hassoc.dvd, hassoc.symm.dvd⟩
              exact False.elim (hrS (heq ▸ hs))
          exact hcop.mul_dvd (hD r (Finset.mem_insert_self r S))
            (ih (fun s hs => hI s (Finset.mem_insert_of_mem hs))
                (fun s hs => hN s (Finset.mem_insert_of_mem hs))
                (fun s hs => hD s (Finset.mem_insert_of_mem hs)))
      exact hprod_dvd Fa
        (fun r hr => hF_irr r (Finset.mem_filter.mp hr).1)
        (fun r hr => hF_norm r (Finset.mem_filter.mp hr).1)
        (fun r hr => (Finset.mem_filter.mp hr).2)
    -- IsCoprime a_rat Ra_rat
    have hcop_a_Ra : IsCoprime a_rat Ra_rat := by
      apply IsCoprime.prod_right
      intro r hr
      have hrF : r ∈ F := (Finset.mem_filter.mp hr).1
      have hrnd : ¬ r ∣ a_rat := (Finset.mem_filter.mp hr).2
      rcases irr_coprime_or_dvd (hF_irr r hrF) a_rat with h | h
      · exact h.symm
      · exact False.elim (hrnd h)
    -- a_rat ∣ Q_rat ^ N for N = (normalizedFactors a_rat).card
    have ha_dvd_Qpow : ∃ N : ℕ, a_rat ∣ Q_rat ^ N := by
      let nf := UniqueFactorizationMonoid.normalizedFactors a_rat
      refine ⟨nf.card, ?_⟩
      have ha_assoc : Associated nf.prod a_rat :=
        UniqueFactorizationMonoid.prod_normalizedFactors ha_rat_ne
      have hdvd_all : ∀ r ∈ nf, r ∣ Q_rat := by
        intro r hr
        have hr_irr : Irreducible r := UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr
        have hr_norm : normalize r = r := UniqueFactorizationMonoid.normalize_normalized_factor r hr
        have hr_dvd_a : r ∣ a_rat := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hr
        have ha_dvd_P : a_rat ∣ P_rat := by
          have : a ∣ P := Finset.dvd_prod_of_mem _ ha
          exact Polynomial.map_dvd emb this
        have hr_dvd_P : r ∣ P_rat := hr_dvd_a.trans ha_dvd_P
        obtain ⟨r', hr'_mem, hr'_assoc⟩ :=
          UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hP_rat_ne hr_irr hr_dvd_P
        have hr'_eq : r' = r := by
          rw [← UniqueFactorizationMonoid.normalize_normalized_factor r' hr'_mem, ← hr_norm]
          exact normalize_eq_normalize_iff.mpr ⟨hr'_assoc.symm.dvd, hr'_assoc.dvd⟩
        rw [← hr'_eq]
        exact Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.mpr hr'_mem)
      have hprod_dvd : ∀ s : Multiset (Polynomial (RatFunc ℝ)),
          (∀ r ∈ s, r ∣ Q_rat) → s.prod ∣ Q_rat ^ s.card := by
        intro s
        induction s using Multiset.induction_on with
        | empty => intro _; simp
        | cons r s ih =>
          intro h
          rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
          exact mul_dvd_mul (h r (Multiset.mem_cons_self r s))
            (ih fun t ht => h t (Multiset.mem_cons_of_mem ht))
      exact ha_assoc.dvd_iff_dvd_left.mp (hprod_dvd nf hdvd_all)
    obtain ⟨N, qpow_rat, hqpow_rat⟩ := ha_dvd_Qpow
    obtain ⟨qdiv_rat, hqdiv_rat⟩ := hQa_dvd_a
    obtain ⟨ua_rat, va_rat, huva_rat⟩ := hcop_a_Ra
    -- Clear denominators of Qa_rat, Ra_rat, qpow_rat, qdiv_rat, ua_rat, va_rat
    obtain ⟨DQa, Qa, hDQa_ne, hQa_eq⟩ := exists_clear_denom Qa_rat
    obtain ⟨DRa, Ra, hDRa_ne, hRa_eq⟩ := exists_clear_denom Ra_rat
    obtain ⟨Dqpow, qpow, hDqpow_ne, hqpow_eq⟩ := exists_clear_denom qpow_rat
    obtain ⟨Dqdiv, qdiv, hDqdiv_ne, hqdiv_eq⟩ := exists_clear_denom qdiv_rat
    obtain ⟨Dua, ua, hDua_ne, hua_eq⟩ := exists_clear_denom ua_rat
    obtain ⟨Dva, va, hDva_ne, hva_eq⟩ := exists_clear_denom va_rat
    -- Polynomial identities in ℝ[x][y]:
    -- 1. C(DQa * DRa) * Q = C(DQ) * Qa * Ra
    have hId1 : Polynomial.C (DQa * DRa) * Q = Polynomial.C DQ * Qa * Ra := by
      apply map_emb_injective
      simp only [Polynomial.map_mul, Polynomial.map_C, ← hQ_eq, ← hQa_eq, ← hRa_eq, hQ_split,
        map_mul, Polynomial.C_mul]
      ring
    -- 2. C(DQ ^ N * Dqpow) * a * qpow = C(Dqpow) * Q ^ N
    have hId2 : Polynomial.C (DQ ^ N) * (a * qpow) = Polynomial.C Dqpow * Q ^ N := by
      apply map_emb_injective
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, ← hQ_eq, ← hqpow_eq,
        map_pow, Polynomial.C_pow]
      have h1 : Polynomial.C (emb DQ) ^ N * (a_rat * (Polynomial.C (emb Dqpow) * qpow_rat)) =
          Polynomial.C (emb Dqpow) * (Polynomial.C (emb DQ) * Q_rat) ^ N := by
        rw [mul_pow, hqpow_rat]; ring
      simpa [a_rat] using h1
    -- 3. C(DQa * Dqdiv) * a = Qa * qdiv
    have hId3 : Polynomial.C (DQa * Dqdiv) * a = Qa * qdiv := by
      apply map_emb_injective
      simp only [Polynomial.map_mul, Polynomial.map_C, ← hQa_eq, ← hqdiv_eq, map_mul, Polynomial.C_mul]
      have h1 : Polynomial.C (emb DQa) * Polynomial.C (emb Dqdiv) * a_rat =
          Polynomial.C (emb DQa) * Qa_rat * (Polynomial.C (emb Dqdiv) * qdiv_rat) := by
        rw [hqdiv_rat]; ring
      simpa [a_rat] using h1
    -- 4. (C(DRa * Dva) * ua) * a + (C(Dua) * va) * Ra = C(DRa * Dua * Dva)
    have hId4 : (Polynomial.C (DRa * Dva) * ua) * a + (Polynomial.C Dua * va) * Ra =
        Polynomial.C (DRa * Dua * Dva) := by
      apply map_emb_injective
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        ← hua_eq, ← hva_eq, ← hRa_eq, map_mul, Polynomial.C_mul]
      have h1 : Polynomial.C (emb DRa) * Polynomial.C (emb Dva) *
          (Polynomial.C (emb Dua) * ua_rat) * a_rat +
          Polynomial.C (emb Dua) * (Polynomial.C (emb Dva) * va_rat) *
          (Polynomial.C (emb DRa) * Ra_rat) =
          Polynomial.C (emb DRa) * Polynomial.C (emb Dua) * Polynomial.C (emb Dva) *
            (ua_rat * a_rat + va_rat * Ra_rat) := by ring
      simpa [a_rat, huva_rat] using h1
    let ca : Polynomial ℝ := DQ * DQa * DRa * Dqpow * Dqdiv * Dua * Dva
    have hca_ne : ca ≠ 0 := by
      simp only [ca, ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨⟨⟨⟨⟨hDQ_ne, hDQa_ne⟩, hDRa_ne⟩, hDqpow_ne⟩, hDqdiv_ne⟩, hDua_ne⟩, hDva_ne⟩
    refine ⟨Ra, ca, hca_ne, ?_, ?_⟩
    · intro x hcx y hay
      have h2 := congrArg (fun p => (p.map (Polynomial.evalRingHom x)).eval y) hId2
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.coe_evalRingHom, hay, zero_mul, mul_zero] at h2
      have hDqpow_x : Dqpow.eval x ≠ 0 := by
        intro h0; apply hcx; simp [ca, h0]
      have hQpow0 : ((Q.map (Polynomial.evalRingHom x)).eval y) ^ N = 0 := by
        rcases mul_eq_zero.mp h2.symm with h | h
        · exact False.elim (hDqpow_x h)
        · exact h
      exact eq_zero_of_pow_eq_zero hQpow0
    · intro x hcx y hQy
      have hDQ_x : DQ.eval x ≠ 0 := fun h0 => hcx (by simp [ca, h0])
      have hDQa_x : DQa.eval x ≠ 0 := fun h0 => hcx (by simp [ca, h0])
      have hDRa_x : DRa.eval x ≠ 0 := fun h0 => hcx (by simp [ca, h0])
      have hDqdiv_x : Dqdiv.eval x ≠ 0 := fun h0 => hcx (by simp [ca, h0])
      have hDua_x : Dua.eval x ≠ 0 := fun h0 => hcx (by simp [ca, h0])
      have hDva_x : Dva.eval x ≠ 0 := fun h0 => hcx (by simp [ca, h0])
      constructor
      · intro hay hRay
        have h4 := congrArg (fun p => (p.map (Polynomial.evalRingHom x)).eval y) hId4
        simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.coe_evalRingHom, hay, hRay, mul_zero, add_zero] at h4
        have hnz : DRa.eval x * Dua.eval x * Dva.eval x ≠ 0 := by
          exact mul_ne_zero (mul_ne_zero hDRa_x hDua_x) hDva_x
        exact hnz h4.symm
      · intro hRay
        have h1 := congrArg (fun p => (p.map (Polynomial.evalRingHom x)).eval y) hId1
        simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.coe_evalRingHom, hQy, mul_zero] at h1
        have hQay : (Qa.map (Polynomial.evalRingHom x)).eval y = 0 := by
          rcases mul_eq_zero.mp h1.symm with h | h
          · rcases mul_eq_zero.mp h with h' | h'
            · exact False.elim (hDQ_x h')
            · exact h'
          · exact False.elim (hRay h)
        have h3 := congrArg (fun p => (p.map (Polynomial.evalRingHom x)).eval y) hId3
        simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.coe_evalRingHom, hQay, zero_mul] at h3
        rcases mul_eq_zero.mp h3 with h | h
        · exact False.elim (mul_ne_zero hDQa_x hDqdiv_x (by simpa using h))
        · exact h
  choose Ra ca hca_ne hca_dvd hca_iff using hper_a
  -- Collect all critical x-values into Crit : Finset ℝ
  let basePoly : Polynomial ℝ := Q.leadingCoeff * (DQ * DQ * Du * Dv)
  have hbase_ne : basePoly ≠ 0 := by
    have hlc_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ_ne
    simp only [basePoly, ne_eq, mul_eq_zero, not_or]
    exact ⟨hlc_ne, ⟨⟨⟨hDQ_ne, hDQ_ne⟩, hDu_ne⟩, hDv_ne⟩⟩
  let Crit : Finset ℝ :=
    basePoly.roots.toFinset ∪ B.attach.biUnion fun a => (ca a.1 a.2).roots.toFinset
  refine ⟨Q, Crit, hQ_ne, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hnot : x ∉ basePoly.roots.toFinset := fun h => hx (Finset.mem_union_left _ h)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hbase_ne] at hnot
    intro h0; apply hnot; simp [basePoly, h0]
  · intro x hx y hQy hQ'y
    have hnot : x ∉ basePoly.roots.toFinset := fun h => hx (Finset.mem_union_left _ h)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hbase_ne] at hnot
    have hbez := congrArg (fun p => (p.map (Polynomial.evalRingHom x)).eval y) hbezQ
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.coe_evalRingHom, ← map_eval_derivative, hQy, hQ'y, mul_zero, add_zero] at hbez
    apply hnot
    simp [basePoly, ← hbez]
  · intro a ha x hx y hay
    have hnot : x ∉ (ca a ha).roots.toFinset := by
      intro h; apply hx
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, h⟩)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hca_ne a ha)] at hnot
    exact hca_dvd a ha x hnot y hay
  · intro a ha
    refine ⟨Ra a ha, fun x hx y hQy => ?_⟩
    have hnot : x ∉ (ca a ha).roots.toFinset := by
      intro h; apply hx
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, h⟩)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hca_ne a ha)] at hnot
    exact hca_iff a ha x hnot y hQy

/-- Full 2D polynomial projection lemma: for any finite set `B` of nonzero polynomials in `ℝ[x][y]`,
there is a finite set `Crit : Finset ℝ` such that on every open connected interval `U` disjoint
from `Crit`, the union of all real `y`-roots of `a ∈ B` consists of `s` continuous, strictly
ordered branches `ξ 0 < ... < ξ (s - 1)`, and each `a ∈ B` vanishes identically or nowhere along
each branch `ξ k`. -/
lemma projection_poly (B : Finset (Polynomial (Polynomial ℝ))) (hB : ∀ a ∈ B, a ≠ 0) :
    ∃ (Crit : Finset ℝ),
      ∀ (U : Set ℝ), IsOpen U → IsConnected U → (∀ x ∈ U, x ∉ Crit) →
        ∃ (s : ℕ) (ξ : Fin s → ℝ → ℝ),
          (∀ x ∈ U, StrictMono (fun k => ξ k x)) ∧
          (∀ k : Fin s, ContinuousOn (ξ k) U) ∧
          (∀ a ∈ B, ∀ x ∈ U, ∀ y : ℝ,
            (a.map (Polynomial.evalRingHom x)).eval y = 0 → ∃ k : Fin s, y = ξ k x) ∧
          (∀ a ∈ B, ∀ k : Fin s,
            (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0) ∨
            (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ k x) ≠ 0)) := by
  obtain ⟨Q, Crit, _, hlc, hsimple, hdvd, hiff⟩ := ratfunc_sqfree_part B hB
  refine ⟨Crit, fun U hU_open hU_conn hU_disj => ?_⟩
  obtain ⟨s, ξ, hmono, hcont, hroots⟩ :=
    connected_simple_roots Q hU_open hU_conn (fun x hx => hlc x (hU_disj x hx))
      (fun x hx => hsimple x (hU_disj x hx))
  refine ⟨s, ξ, hmono, hcont, ?_, ?_⟩
  · intro a ha x hx y hay
    exact (hroots x hx y).mp (hdvd a ha x (hU_disj x hx) y hay)
  · intro a ha k
    obtain ⟨R, hR⟩ := hiff a ha
    let Z : Set ℝ := {x ∈ U | (a.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0}
    let NZ : Set ℝ := {x ∈ U | (R.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0}
    have hZ_cont : ContinuousOn (fun x => (a.map (Polynomial.evalRingHom x)).eval (ξ k x)) U :=
      (eval_polyY_continuous a).comp_continuousOn (continuousOn_id.prodMk (hcont k))
    have hNZ_cont : ContinuousOn (fun x => (R.map (Polynomial.evalRingHom x)).eval (ξ k x)) U :=
      (eval_polyY_continuous R).comp_continuousOn (continuousOn_id.prodMk (hcont k))
    have hZ_closed : IsClosed (Subtype.val ⁻¹' Z : Set U) := by
      have : (Subtype.val ⁻¹' Z : Set U) =
          (fun x : U => (a.map (Polynomial.evalRingHom x.1)).eval (ξ k x.1)) ⁻¹' {0} := by
        ext ⟨x, hx⟩; simp [Z, hx]
      rw [this]
      exact isClosed_singleton.preimage (continuousOn_iff_continuous_restrict.mp hZ_cont)
    have hNZ_closed : IsClosed (Subtype.val ⁻¹' NZ : Set U) := by
      have : (Subtype.val ⁻¹' NZ : Set U) =
          (fun x : U => (R.map (Polynomial.evalRingHom x.1)).eval (ξ k x.1)) ⁻¹' {0} := by
        ext ⟨x, hx⟩; simp [NZ, hx]
      rw [this]
      exact isClosed_singleton.preimage (continuousOn_iff_continuous_restrict.mp hNZ_cont)
    have hpart : ∀ x : U, x ∈ (Subtype.val ⁻¹' Z : Set U) ↔ x ∉ (Subtype.val ⁻¹' NZ : Set U) := by
      intro ⟨x, hx⟩
      have hQ0 : (Q.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0 :=
        (hroots x hx (ξ k x)).mpr ⟨k, rfl⟩
      simpa [Z, NZ, hx] using hR x (hU_disj x hx) (ξ k x) hQ0
    have hZ_clopen : IsClopen (Subtype.val ⁻¹' Z : Set U) := by
      refine ⟨hZ_closed, ?_⟩
      have : (Subtype.val ⁻¹' Z : Set U) = (Subtype.val ⁻¹' NZ : Set U)ᶜ := by
        ext x; exact hpart x
      rw [this]
      exact hNZ_closed.isOpen_compl
    haveI : ConnectedSpace U := Subtype.connectedSpace hU_conn
    rcases isClopen_iff.mp hZ_clopen with hemp | huniv
    · right
      intro x hx h0
      have : (⟨x, hx⟩ : U) ∈ (∅ : Set U) := by
        rw [← hemp]; exact ⟨hx, h0⟩
      exact this
    · left
      intro x hx
      have : (⟨x, hx⟩ : U) ∈ (Subtype.val ⁻¹' Z : Set U) := by rw [huniv]; trivial
      exact this.2

/- ## Part 5: Mahé's Lemma and Vertical Strip Representatives -/

noncomputable def remY (a : Polynomial (Polynomial ℝ)) : Polynomial (Polynomial ℝ) :=
  a - Polynomial.C (Polynomial.C (1 / (a.natDegree : ℝ))) * Polynomial.X * a.derivative

lemma natDegree_remY_lt {a : Polynomial (Polynomial ℝ)} (hd : 0 < a.natDegree) :
    (remY a).natDegree < a.natDegree := by
  have hle : (remY a).natDegree ≤ a.natDegree := by
    have h1 : (Polynomial.C (Polynomial.C (1 / (a.natDegree : ℝ))) * Polynomial.X *
        a.derivative).natDegree ≤
        (Polynomial.C (Polynomial.C (1 / (a.natDegree : ℝ))) * Polynomial.X).natDegree +
        a.derivative.natDegree := Polynomial.natDegree_mul_le
    have h2 : (Polynomial.C (Polynomial.C (1 / (a.natDegree : ℝ))) * Polynomial.X).natDegree ≤ 1 := by
      calc _ ≤ (Polynomial.C (Polynomial.C (1 / (a.natDegree : ℝ)))).natDegree +
              (Polynomial.X : Polynomial (Polynomial ℝ)).natDegree := Polynomial.natDegree_mul_le
        _ = 1 := by simp
    have h3 : a.derivative.natDegree ≤ a.natDegree - 1 := Polynomial.natDegree_derivative_le a
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le le_rfl (by omega))
  have hcoeff : (remY a).coeff a.natDegree = 0 := by
    simp only [remY, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul]
    have hX : (Polynomial.X * a.derivative).coeff a.natDegree = a.derivative.coeff (a.natDegree - 1) := by
      have : a.natDegree = (a.natDegree - 1) + 1 := (Nat.sub_add_cancel hd).symm
      conv_lhs => rw [this]
      exact Polynomial.coeff_X_mul a.derivative (a.natDegree - 1)
    rw [hX, Polynomial.coeff_derivative]
    have hadd : a.natDegree - 1 + 1 = a.natDegree := Nat.sub_add_cancel hd
    rw [hadd]
    have hne : (a.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hmul : Polynomial.C (1 / (a.natDegree : ℝ)) * (a.natDegree : Polynomial ℝ) = 1 := by
      rw [← Polynomial.C_eq_natCast, ← map_mul, one_div_mul_cancel hne, map_one]
    rw [mul_left_comm, ← Nat.cast_succ, Nat.succ_eq_add_one, hadd, hmul, mul_one, sub_self]
  by_contra hge
  have heq : (remY a).natDegree = a.natDegree := le_antisymm hle (not_lt.mp hge)
  by_cases hr0 : remY a = 0
  · rw [hr0, Polynomial.natDegree_zero] at heq; omega
  · have hlc := Polynomial.leadingCoeff_ne_zero.mpr hr0
    rw [Polynomial.leadingCoeff, heq] at hlc
    exact hlc hcoeff

lemma eval_remY (a : Polynomial (Polynomial ℝ)) (x y : ℝ) :
    ((remY a).map (Polynomial.evalRingHom x)).eval y =
      (a.map (Polynomial.evalRingHom x)).eval y -
      (1 / (a.natDegree : ℝ)) * y * (a.map (Polynomial.evalRingHom x)).derivative.eval y := by
  simp only [remY, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.coe_evalRingHom, ← map_eval_derivative]

lemma remY_neg (a : Polynomial (Polynomial ℝ)) : remY (-a) = -remY a := by
  simp only [remY, Polynomial.natDegree_neg, Polynomial.derivative_neg]
  ring

lemma exists_closure_single : ∀ (d : ℕ) (a : Polynomial (Polynomial ℝ)), a.natDegree ≤ d →
    ∃ B : Finset (Polynomial (Polynomial ℝ)),
      (∀ b ∈ B, b ≠ 0) ∧
      (a ≠ 0 → a ∈ B) ∧
      (∀ b ∈ B, -b ∈ B) ∧
      (∀ b ∈ B, b.derivative ≠ 0 → b.derivative ∈ B) ∧
      (∀ b ∈ B, 0 < b.natDegree → remY b ≠ 0 → remY b ∈ B) := by
  classical
  intro d
  induction d with
  | zero =>
    intro a ha
    by_cases ha0 : a = 0
    · exact ⟨∅, by simp, fun h => False.elim (h ha0), by simp, by simp, by simp⟩
    · refine ⟨{a, -a}, ?_, by simp, ?_, ?_, ?_⟩
      · intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact ha0
        · exact neg_ne_zero.mpr ha0
      · intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
        rcases hb with rfl | rfl <;> simp
      · intro b hb hb'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        have hdeg0 : b.natDegree = 0 := by
          rcases hb with rfl | rfl
          · omega
          · rw [Polynomial.natDegree_neg]; omega
        rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, Polynomial.derivative_C] at hb'
        exact False.elim (hb' rfl)
      · intro b hb hpos
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · omega
        · rw [Polynomial.natDegree_neg] at hpos; omega
  | succ d ih =>
    intro a ha
    by_cases ha0 : a = 0
    · exact ⟨∅, by simp, fun h => False.elim (h ha0), by simp, by simp, by simp⟩
    · by_cases hdeg0 : a.natDegree = 0
      · exact ih a (by omega)
      · have hpos : 0 < a.natDegree := Nat.pos_of_ne_zero hdeg0
        have hd1 : a.derivative.natDegree ≤ d := by
          have := Polynomial.natDegree_derivative_le a; omega
        have hd2 : (remY a).natDegree ≤ d := by
          have := natDegree_remY_lt hpos; omega
        obtain ⟨B1, hB1_nz, hB1_mem, hB1_neg, hB1_der, hB1_rem⟩ := ih a.derivative hd1
        obtain ⟨B2, hB2_nz, hB2_mem, hB2_neg, hB2_der, hB2_rem⟩ := ih (remY a) hd2
        refine ⟨{a, -a} ∪ B1 ∪ B2, ?_, by simp, ?_, ?_, ?_⟩
        · intro b hb
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with ((rfl | rfl) | h) | h
          · exact ha0
          · exact neg_ne_zero.mpr ha0
          · exact hB1_nz b h
          · exact hB2_nz b h
        · intro b hb
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hb ⊢
          rcases hb with ((rfl | rfl) | h) | h
          · left; left; right; rfl
          · left; left; left; simp
          · left; right; exact hB1_neg b h
          · right; exact hB2_neg b h
        · intro b hb hb'
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hb ⊢
          rcases hb with ((rfl | rfl) | h) | h
          · left; right; exact hB1_mem hb'
          · left; right
            rw [Polynomial.derivative_neg] at hb' ⊢
            exact hB1_neg _ (hB1_mem (neg_ne_zero.mp hb'))
          · left; right; exact hB1_der b h hb'
          · right; exact hB2_der b h hb'
        · intro b hb hbp hbr
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hb ⊢
          rcases hb with ((rfl | rfl) | h) | h
          · right; exact hB2_mem hbr
          · right
            rw [remY_neg] at hbr ⊢
            exact hB2_neg _ (hB2_mem (neg_ne_zero.mp hbr))
          · left; right; exact hB1_rem b h hbp hbr
          · right; exact hB2_rem b h hbp hbr

lemma exists_polyY_closure (A : Finset (Polynomial (Polynomial ℝ))) :
    ∃ B : Finset (Polynomial (Polynomial ℝ)),
      (∀ a ∈ B, a ≠ 0) ∧
      (∀ a ∈ A, a ≠ 0 → a ∈ B) ∧
      (∀ a ∈ B, -a ∈ B) ∧
      (∀ a ∈ B, a.derivative ≠ 0 → a.derivative ∈ B) ∧
      (∀ a ∈ B, 0 < a.natDegree → remY a ≠ 0 → remY a ∈ B) := by
  classical
  choose B hB_nz hB_mem hB_neg hB_der hB_rem using
    fun a : Polynomial (Polynomial ℝ) => exists_closure_single a.natDegree a le_rfl
  refine ⟨A.biUnion B, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp ha
    exact hB_nz c a hc
  · intro a ha ha0
    exact Finset.mem_biUnion.mpr ⟨a, ha, hB_mem a ha0⟩
  · intro a ha
    obtain ⟨c, hcA, hc⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨c, hcA, hB_neg c a hc⟩
  · intro a ha ha'
    obtain ⟨c, hcA, hc⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨c, hcA, hB_der c a hc ha'⟩
  · intro a ha hap har
    obtain ⟨c, hcA, hc⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨c, hcA, hB_rem c a hc hap har⟩

lemma poly_pos_right_of_root {p : Polynomial ℝ} {r b : ℝ} (hr : p.eval r = 0)
    (hdr : 0 < p.derivative.eval r) (hno : ∀ y, r < y → y < b → p.eval y ≠ 0) :
    ∀ y, r < y → y < b → 0 < p.eval y := by
  have hhd := Polynomial.hasDerivAt p r
  have htend : Filter.Tendsto (fun y => (p.eval y - p.eval r) / (y - r))
      (nhdsWithin r {r}ᶜ) (nhds (p.derivative.eval r)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hhd
    have hfun : slope (fun x => p.eval x) r = fun y => (p.eval y - p.eval r) / (y - r) := by
      funext y; simp [slope_def_field]
    rwa [hfun] at h
  have hev := (tendsto_order.mp htend).1 0 hdr
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ_pos, hδ⟩ := hev
  intro y hyr hyb
  let y0 := min (r + δ / 2) ((r + y) / 2)
  have hy0_gt : r < y0 := lt_min (by linarith) (by linarith)
  have hy0_lt_y : y0 < y := (min_le_right _ _).trans_lt (by linarith)
  have hy0_pos : 0 < p.eval y0 := by
    have hdist : dist y0 r < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      have : y0 ≤ r + δ / 2 := min_le_left _ _
      linarith
    have hq := hδ hdist (ne_of_gt hy0_gt)
    rw [hr, sub_zero] at hq
    exact (div_pos_iff_of_pos_right (by linarith : 0 < y0 - r)).mp hq
  by_contra hle
  have hneg : p.eval y < 0 := lt_of_le_of_ne (not_lt.mp hle) (hno y hyr hyb)
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hy0_lt_y.le p.continuous.continuousOn ⟨hneg.le, hy0_pos.le⟩
  exact hno z (lt_of_lt_of_le hy0_gt hz.1) (lt_of_le_of_lt hz.2 hyb) hz0

lemma poly_neg_left_of_root {p : Polynomial ℝ} {a r : ℝ} (hr : p.eval r = 0)
    (hdr : 0 < p.derivative.eval r) (hno : ∀ y, a < y → y < r → p.eval y ≠ 0) :
    ∀ y, a < y → y < r → p.eval y < 0 := by
  have hhd := Polynomial.hasDerivAt p r
  have htend : Filter.Tendsto (fun y => (p.eval y - p.eval r) / (y - r))
      (nhdsWithin r {r}ᶜ) (nhds (p.derivative.eval r)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hhd
    have hfun : slope (fun x => p.eval x) r = fun y => (p.eval y - p.eval r) / (y - r) := by
      funext y; simp [slope_def_field]
    rwa [hfun] at h
  have hev := (tendsto_order.mp htend).1 0 hdr
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ_pos, hδ⟩ := hev
  intro y hay hyr
  let y0 := max (r - δ / 2) ((y + r) / 2)
  have hy0_lt : y0 < r := max_lt (by linarith) (by linarith)
  have hy_lt_y0 : y < y0 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hy0_neg : p.eval y0 < 0 := by
    have hdist : dist y0 r < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have : r - δ / 2 ≤ y0 := le_max_left _ _
      linarith
    have hq := hδ hdist (ne_of_lt hy0_lt)
    rw [hr, sub_zero] at hq
    have hneg_den : y0 - r < 0 := by linarith
    have : 0 < (-p.eval y0) / (-(y0 - r)) := by
      rw [neg_div_neg_eq]; exact hq
    have hpos_num := (div_pos_iff_of_pos_right (by linarith : 0 < -(y0 - r))).mp this
    linarith
  by_contra hge
  have hpos : 0 < p.eval y := lt_of_le_of_ne (not_lt.mp hge) (Ne.symm (hno y hay hyr))
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hy_lt_y0.le p.continuous.continuousOn ⟨hy0_neg.le, hpos.le⟩
  exact hno z (lt_of_lt_of_le hay hz.1) (lt_of_le_of_lt hz.2 hy0_lt) hz0

lemma poly_pos_of_pos_no_root {p : Polynomial ℝ} {a b : ℝ} (ha : 0 < p.eval a)
    (hno : ∀ y, a < y → y < b → p.eval y ≠ 0) :
    ∀ y, a ≤ y → y < b → 0 < p.eval y := by
  intro y hay hyb
  rcases eq_or_lt_of_le hay with rfl | hlt
  · exact ha
  · by_contra hle
    have hneg : p.eval y < 0 := lt_of_le_of_ne (not_lt.mp hle) (hno y hlt hyb)
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hlt.le p.continuous.continuousOn ⟨hneg.le, ha.le⟩
    rcases eq_or_lt_of_le hz.1 with rfl | hza
    · linarith
    · exact hno z hza (lt_of_le_of_lt hz.2 hyb) hz0

lemma poly_pos_ray_of_root {p : Polynomial ℝ} {r : ℝ} (hr : p.eval r = 0)
    (hdr : 0 < p.derivative.eval r) (hno : ∀ y, r < y → p.eval y ≠ 0) :
    ∀ y, r < y → 0 < p.eval y :=
  fun y hy => poly_pos_right_of_root (b := y + 1) hr hdr (fun z h1 _ => hno z h1) y hy (by linarith)

lemma poly_neg_ray_of_root {p : Polynomial ℝ} {r : ℝ} (hr : p.eval r = 0)
    (hdr : 0 < p.derivative.eval r) (hno : ∀ y, y < r → p.eval y ≠ 0) :
    ∀ y, y < r → p.eval y < 0 :=
  fun y hy => poly_neg_left_of_root (a := y - 1) hr hdr (fun z _ h2 => hno z h2) y (by linarith) hy

lemma mahe_truncation (B : Finset (Polynomial (Polynomial ℝ)))
    (hB_neg : ∀ a ∈ B, -a ∈ B)
    (hB_der : ∀ a ∈ B, a.derivative ≠ 0 → a.derivative ∈ B)
    (hB_rem : ∀ a ∈ B, 0 < a.natDegree → remY a ≠ 0 → remY a ∈ B)
    {U : Set ℝ} (hU_conn : IsConnected U)
    {s : ℕ} {ξ : Fin s → ℝ → ℝ}
    (hmono : ∀ x ∈ U, StrictMono (fun k => ξ k x))
    (hcont : ∀ k : Fin s, ContinuousOn (ξ k) U)
    (hroots : ∀ a ∈ B, ∀ x ∈ U, ∀ y : ℝ,
      (a.map (Polynomial.evalRingHom x)).eval y = 0 → ∃ k : Fin s, y = ξ k x)
    (hdich : ∀ a ∈ B, ∀ k : Fin s,
      (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0) ∨
      (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ k x) ≠ 0)) :
    ∀ (d : ℕ) (a : Polynomial (Polynomial ℝ)), a ∈ B → a.natDegree ≤ d →
      ∀ (k : Fin s), (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0) →
        ∃ c : (Fin 2 → ℝ) → ℝ, SI c ∧
          ∀ x ∈ U, ∀ y : ℝ,
            c (fun i => if i = 0 then x else y) =
              if ξ k x < y then (a.map (Polynomial.evalRingHom x)).eval y else 0 := by
  classical
  intro d
  induction d with
  | zero =>
    intro a ha hdeg k hk
    obtain ⟨x₀, hx₀⟩ := hU_conn.nonempty
    have hd0 : a.natDegree = 0 := by omega
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have h0 : (a.map (Polynomial.evalRingHom x₀)).eval (ξ k x₀) = 0 := hk x₀ hx₀
    -- If a = C p vanishes at (x₀, ξ k x₀), then p(x₀) = 0, so a(x₀, y) = 0 for all y,
    -- which contradicts hroots (a has only finitely many roots at x₀)!
    have hall : ∀ y : ℝ, (a.map (Polynomial.evalRingHom x₀)).eval y = 0 := by
      intro y
      rw [hconst] at h0 ⊢
      simpa using h0
    -- Pick y larger than all ξ j x₀
    let M : ℝ := 1 + Finset.univ.sup' ⟨k, Finset.mem_univ k⟩ (fun j => |ξ j x₀|)
    obtain ⟨j, hj⟩ := hroots a ha x₀ hx₀ M (hall M)
    have hle : ξ j x₀ ≤ |ξ j x₀| := le_abs_self _
    have hle2 : |ξ j x₀| ≤ Finset.univ.sup' ⟨k, Finset.mem_univ k⟩ (fun j => |ξ j x₀|) :=
      Finset.le_sup' (fun j => |ξ j x₀|) (Finset.mem_univ j)
    linarith
  | succ d ih_deg =>
    -- Prove for all a ∈ B with a.natDegree ≤ d + 1, by strong induction on k.val
    intro a ha hdeg k
    suffices ∀ (n : ℕ) (hn : n < s),
        (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ ⟨n, hn⟩ x) = 0) →
        ∃ c : (Fin 2 → ℝ) → ℝ, SI c ∧
          ∀ x ∈ U, ∀ y : ℝ,
            c (fun i => if i = 0 then x else y) =
              if ξ ⟨n, hn⟩ x < y then (a.map (Polynomial.evalRingHom x)).eval y else 0 from
      this k.val k.isLt
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih_n =>
      intro hn hk
      let k : Fin s := ⟨n, hn⟩
      have ih_k : ∀ j : Fin s, j < k →
          (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0) →
          ∃ c : (Fin 2 → ℝ) → ℝ, SI c ∧
            ∀ x ∈ U, ∀ y : ℝ,
              c (fun i => if i = 0 then x else y) =
                if ξ j x < y then (a.map (Polynomial.evalRingHom x)).eval y else 0 :=
        fun j hjk hj => ih_n j.val hjk j.isLt hj
      by_cases hdeg_le : a.natDegree ≤ d
      · exact ih_deg a ha hdeg_le k hk
      · have hdeg_eq : a.natDegree = d + 1 := by omega
        have hdeg_pos : 0 < a.natDegree := by omega
        -- Helper: build c_prev (equal to a above previous root of a, or a everywhere if none)
        have hprev : ∃ (c_prev : (Fin 2 → ℝ) → ℝ), SI c_prev ∧
            (∀ x ∈ U, ∀ y : ℝ, ξ k x < y →
              c_prev (fun i => if i = 0 then x else y) = (a.map (Polynomial.evalRingHom x)).eval y) ∧
            (∀ x ∈ U, ∀ y : ℝ, y ≤ ξ k x →
              (∀ j : Fin s, j < k → (a.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0 → ξ j x < y) →
              c_prev (fun i => if i = 0 then x else y) = (a.map (Polynomial.evalRingHom x)).eval y) ∧
            (∀ x ∈ U, ∀ y : ℝ,
              (∃ j : Fin s, j < k ∧ (a.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0 ∧ y ≤ ξ j x) →
              c_prev (fun i => if i = 0 then x else y) = 0) := by
          let prevSet : Finset (Fin s) :=
            Finset.univ.filter fun j => j < k ∧ ∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0
          by_cases hpne : prevSet.Nonempty
          · let j0 : Fin s := prevSet.max' hpne
            have hj0_mem : j0 ∈ prevSet := Finset.max'_mem prevSet hpne
            have hj0_lt : j0 < k := (Finset.mem_filter.mp hj0_mem).2.1
            have hj0_root : ∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ j0 x) = 0 :=
              (Finset.mem_filter.mp hj0_mem).2.2
            obtain ⟨c0, hc0_SI, hc0_eq⟩ := ih_k j0 hj0_lt hj0_root
            refine ⟨c0, hc0_SI, ?_, ?_, ?_⟩
            · intro x hx y hy
              rw [hc0_eq x hx y, if_pos ((hmono x hx hj0_lt).trans hy)]
            · intro x hx y _ hgt
              rw [hc0_eq x hx y, if_pos (hgt j0 hj0_lt (hj0_root x hx))]
            · intro x hx y ⟨j, hjk, hjx, hyj⟩
              have hj_all : ∀ x' ∈ U, (a.map (Polynomial.evalRingHom x')).eval (ξ j x') = 0 := by
                rcases hdich a ha j with h | h
                · exact h
                · exact False.elim (h x hx hjx)
              have hj_in : j ∈ prevSet := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjk, hj_all⟩
              have hj_le : j ≤ j0 := Finset.le_max' prevSet j hj_in
              have hξ_le : ξ j x ≤ ξ j0 x := (hmono x hx).monotone hj_le
              rw [hc0_eq x hx y, if_neg (not_lt.mpr (hyj.trans hξ_le))]
          · rw [Finset.not_nonempty_iff_eq_empty] at hpne
            refine ⟨fun z => MvPolynomial.eval z (fromPolyY a), SI_poly (fromPolyY a), ?_, ?_, ?_⟩
            · intro x _ y _; simp [eval_fromPolyY]
            · intro x _ y _ _; simp [eval_fromPolyY]
            · intro x hx y ⟨j, hjk, hjx, _⟩
              have hj_all : ∀ x' ∈ U, (a.map (Polynomial.evalRingHom x')).eval (ξ j x') = 0 := by
                rcases hdich a ha j with h | h
                · exact h
                · exact False.elim (h x hx hjx)
              have : j ∈ prevSet := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjk, hj_all⟩
              rw [hpne] at this; exact False.elim (Finset.notMem_empty j this)
        -- Helper: core positive-derivative or zero-derivative construction for any b ∈ B with same degree
        -- First check if a.derivative = 0 (impossible since a.natDegree = d + 1 > 0 and char ℝ = 0)
        have ha'_ne : a.derivative ≠ 0 := by
          intro h0
          have h1 := congrArg (fun p => p.coeff d) h0
          rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at h1
          have hlc : a.coeff (d + 1) ≠ 0 := by
            rw [← hdeg_eq]; exact Polynomial.leadingCoeff_ne_zero.mpr (by
              intro ha0; rw [ha0, Polynomial.natDegree_zero] at hdeg_eq; omega)
          have hd1_ne : ((d + 1 : ℕ) : Polynomial ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          exact mul_ne_zero hlc hd1_ne (by simpa using h1)
        have ha'_B : a.derivative ∈ B := hB_der a ha ha'_ne
        have ha'_deg : a.derivative.natDegree ≤ d := by
          have := Polynomial.natDegree_derivative_le a; omega
        have hra_deg : (remY a).natDegree ≤ d := by
          have := natDegree_remY_lt hdeg_pos; omega
        -- Case 1: a.derivative vanishes on ξ k
        rcases hdich a.derivative ha'_B k with ha'_zero | ha'_nz
        · obtain ⟨ca', hca'_SI, hca'_eq⟩ := ih_deg a.derivative ha'_B ha'_deg k ha'_zero
          have hcr : ∃ cr : (Fin 2 → ℝ) → ℝ, SI cr ∧
              ∀ x ∈ U, ∀ y : ℝ, cr (fun i => if i = 0 then x else y) =
                if ξ k x < y then ((remY a).map (Polynomial.evalRingHom x)).eval y else 0 := by
            by_cases hr0 : remY a = 0
            · refine ⟨fun _ => 0, by simpa using SI_poly 0, fun x _ y => ?_⟩
              simp [hr0]
            · have hrB : remY a ∈ B := hB_rem a ha hdeg_pos hr0
              have hr_zero : ∀ x ∈ U, ((remY a).map (Polynomial.evalRingHom x)).eval (ξ k x) = 0 := by
                intro x hx
                rw [eval_remY, hk x hx, map_eval_derivative, ha'_zero x hx]
                ring
              exact ih_deg (remY a) hrB hra_deg k hr_zero
          obtain ⟨cr, hcr_SI, hcr_eq⟩ := hcr
          let g_fn : (Fin 2 → ℝ) → ℝ := fun z =>
            MvPolynomial.eval z (MvPolynomial.C (1 / (a.natDegree : ℝ)) * MvPolynomial.X 1) * ca' z + cr z
          have hg_SI : SI g_fn := SI_add (SI_mul_poly _ hca'_SI) hcr_SI
          refine ⟨g_fn, hg_SI, fun x hx y => ?_⟩
          have hev_y : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y)
              (MvPolynomial.C (1 / (a.natDegree : ℝ)) * MvPolynomial.X 1) =
              (1 / (a.natDegree : ℝ)) * y := by simp
          dsimp only [g_fn]
          rw [hev_y, hca'_eq x hx y, hcr_eq x hx y]
          split_ifs with hy
          · rw [eval_remY, map_eval_derivative]; ring
          · ring
        · -- Case 2: a.derivative is nowhere zero on ξ k; it has constant strict sign on connected U.
          have ha'_sign : (∀ x ∈ U, 0 < (a.derivative.map (Polynomial.evalRingHom x)).eval (ξ k x)) ∨
              (∀ x ∈ U, (a.derivative.map (Polynomial.evalRingHom x)).eval (ξ k x) < 0) := by
            let f' : ℝ → ℝ := fun x => (a.derivative.map (Polynomial.evalRingHom x)).eval (ξ k x)
            have hf'_cont : ContinuousOn f' U :=
              (eval_polyY_continuous a.derivative).comp_continuousOn (continuousOn_id.prodMk (hcont k))
            obtain ⟨x₀, hx₀⟩ := hU_conn.nonempty
            rcases lt_or_gt_of_ne (ha'_nz x₀ hx₀) with hneg | hpos
            · right
              intro x hx
              by_contra hge
              have hpos' : 0 < f' x := lt_of_le_of_ne (not_lt.mp hge) (Ne.symm (ha'_nz x hx))
              have h0mem : (0 : ℝ) ∈ f' '' U :=
                hU_conn.isPreconnected.intermediate_value hx₀ hx hf'_cont ⟨hneg.le, hpos'.le⟩
              obtain ⟨x1, hx1, hx1_0⟩ := h0mem
              exact ha'_nz x1 hx1 hx1_0
            · left
              intro x hx
              by_contra hle
              have hneg' : f' x < 0 := lt_of_le_of_ne (not_lt.mp hle) (ha'_nz x hx)
              have h0mem : (0 : ℝ) ∈ f' '' U :=
                hU_conn.isPreconnected.intermediate_value hx hx₀ hf'_cont ⟨hneg'.le, hpos.le⟩
              obtain ⟨x1, hx1, hx1_0⟩ := h0mem
              exact ha'_nz x1 hx1 hx1_0
          -- Helper for the positive-derivative case (applied to a or -a)
          have hpos_case : ∀ (b : Polynomial (Polynomial ℝ)) (hb : b ∈ B)
              (hb_deg : b.natDegree = d + 1)
              (hb_root : ∀ x ∈ U, (b.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0)
              (hb'_pos : ∀ x ∈ U, 0 < (b.derivative.map (Polynomial.evalRingHom x)).eval (ξ k x))
              (c_prev : (Fin 2 → ℝ) → ℝ) (hc_prev_SI : SI c_prev)
              (hc_prev_gt : ∀ x ∈ U, ∀ y : ℝ, ξ k x < y →
                c_prev (fun i => if i = 0 then x else y) = (b.map (Polynomial.evalRingHom x)).eval y)
              (hc_prev_mid : ∀ x ∈ U, ∀ y : ℝ, y ≤ ξ k x →
                (∀ j : Fin s, j < k → (b.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0 → ξ j x < y) →
                c_prev (fun i => if i = 0 then x else y) = (b.map (Polynomial.evalRingHom x)).eval y)
              (hc_prev_le : ∀ x ∈ U, ∀ y : ℝ,
                (∃ j : Fin s, j < k ∧ (b.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0 ∧ y ≤ ξ j x) →
                c_prev (fun i => if i = 0 then x else y) = 0),
              ∃ c : (Fin 2 → ℝ) → ℝ, SI c ∧
                ∀ x ∈ U, ∀ y : ℝ, c (fun i => if i = 0 then x else y) =
                  if ξ k x < y then (b.map (Polynomial.evalRingHom x)).eval y else 0 := by
            intro b hb hb_deg hb_root hb'_pos c_prev hc_prev_SI hc_prev_gt hc_prev_mid hc_prev_le
            have hb_deg_pos : 0 < b.natDegree := by omega
            have hb'_ne : b.derivative ≠ 0 := by
              obtain ⟨x₀, hx₀⟩ := hU_conn.nonempty
              intro h0
              have := hb'_pos x₀ hx₀
              rw [h0, Polynomial.map_zero, Polynomial.eval_zero] at this
              exact lt_irrefl 0 this
            have hb'_B : b.derivative ∈ B := hB_der b hb hb'_ne
            have hb'_deg : b.derivative.natDegree ≤ d := by
              have := Polynomial.natDegree_derivative_le b; omega
            have hrb_deg : (remY b).natDegree ≤ d := by
              have := natDegree_remY_lt hb_deg_pos; omega
            -- On (prev root, ξ k x], b ≤ 0!
            have hb_nonpos_mid : ∀ x ∈ U, ∀ y : ℝ, y ≤ ξ k x →
                (∀ j : Fin s, j < k → (b.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0 → ξ j x < y) →
                (b.map (Polynomial.evalRingHom x)).eval y ≤ 0 := by
              intro x hx y hyk hgt
              rcases eq_or_lt_of_le hyk with rfl | hlt
              · rw [hb_root x hx]
              · have hdr : 0 < (b.map (Polynomial.evalRingHom x)).derivative.eval (ξ k x) := by
                  rw [map_eval_derivative]; exact hb'_pos x hx
                have hno_y : ∀ z, y ≤ z → z < ξ k x → (b.map (Polynomial.evalRingHom x)).eval z ≠ 0 := by
                  intro z hyz hzk hz0
                  obtain ⟨j, rfl⟩ := hroots b hb x hx z hz0
                  have hjk : j < k := (hmono x hx).lt_iff_lt.mp hzk
                  linarith [hgt j hjk hz0]
                -- Apply poly_neg_left_of_root on (y, ξ k x) to (y + ξ k x)/2, then continuity/no-root at y!
                have hmid_neg : (b.map (Polynomial.evalRingHom x)).eval ((y + ξ k x) / 2) < 0 :=
                  poly_neg_left_of_root (hb_root x hx) hdr (fun z h1 h2 => hno_y z h1.le h2)
                    ((y + ξ k x) / 2) (by linarith) (by linarith)
                by_contra hpos
                have hpy : 0 < (b.map (Polynomial.evalRingHom x)).eval y :=
                  lt_of_le_of_ne (not_le.mp hpos).le (Ne.symm (hno_y y le_rfl hlt))
                obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' (by linarith : y ≤ (y + ξ k x) / 2)
                  (b.map (Polynomial.evalRingHom x)).continuous.continuousOn ⟨hmid_neg.le, hpy.le⟩
                exact hno_y z hz.1 (by linarith [hz.2]) hz0
            -- Find smallest k₁ > k where b.derivative vanishes on ξ k₁
            let derSet : Finset (Fin s) :=
              Finset.univ.filter fun j => k < j ∧
                ∀ x ∈ U, (b.derivative.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0
            by_cases hdne : derSet.Nonempty
            · -- Subcase B2: k₁ exists
              let k1 : Fin s := derSet.min' hdne
              have hk1_mem : k1 ∈ derSet := Finset.min'_mem derSet hdne
              have hk1_gt : k < k1 := (Finset.mem_filter.mp hk1_mem).2.1
              have hk1_root : ∀ x ∈ U, (b.derivative.map (Polynomial.evalRingHom x)).eval (ξ k1 x) = 0 :=
                (Finset.mem_filter.mp hk1_mem).2.2
              -- b' has no roots in (ξ k x, ξ k1 x), so b' > 0 on [ξ k x, ξ k1 x), hence b > 0 on (ξ k x, ξ k1 x]!
              have hb_pos_on_k1 : ∀ x ∈ U, ∀ y : ℝ, ξ k x < y → y ≤ ξ k1 x →
                  0 < (b.map (Polynomial.evalRingHom x)).eval y := by
                intro x hx y hy1 hy2
                have hb'_no : ∀ z, ξ k x < z → z < ξ k1 x →
                    (b.derivative.map (Polynomial.evalRingHom x)).eval z ≠ 0 := by
                  intro z hz1 hz2 hz0
                  obtain ⟨j, rfl⟩ := hroots b.derivative hb'_B x hx z hz0
                  have hkj : k < j := (hmono x hx).lt_iff_lt.mp hz1
                  have hjk1 : j < k1 := (hmono x hx).lt_iff_lt.mp hz2
                  have hj_all : ∀ x' ∈ U, (b.derivative.map (Polynomial.evalRingHom x')).eval (ξ j x') = 0 := by
                    rcases hdich b.derivative hb'_B j with h | h
                    · exact h
                    · exact False.elim (h x hx hz0)
                  have hj_in : j ∈ derSet := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hkj, hj_all⟩
                  have := Finset.min'_le derSet j hj_in
                  exact not_le.mpr hjk1 this
                have hb'_pos_Ico : ∀ z, ξ k x ≤ z → z < ξ k1 x →
                    0 < (b.map (Polynomial.evalRingHom x)).derivative.eval z := by
                  intro z hz1 hz2
                  rw [map_eval_derivative]
                  exact poly_pos_of_pos_no_root (hb'_pos x hx) hb'_no z hz1 hz2
                have hmono_b : StrictMonoOn (fun z => (b.map (Polynomial.evalRingHom x)).eval z)
                    (Set.Icc (ξ k x) (ξ k1 x)) := by
                  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
                  · exact (b.map (Polynomial.evalRingHom x)).continuous.continuousOn
                  · intro z hz
                    rw [interior_Icc] at hz
                    rw [(Polynomial.hasDerivAt _ z).deriv]
                    exact hb'_pos_Ico z hz.1.le hz.2
                have hlt := hmono_b (a := ξ k x) (b := y) ⟨le_rfl, (hmono x hx hk1_gt).le⟩ ⟨hy1.le, hy2⟩ hy1
                dsimp only at hlt
                rwa [hb_root x hx] at hlt
              -- At ξ k1 x, remY b = b > 0!
              have hrb_pos_k1 : ∀ x ∈ U, 0 < ((remY b).map (Polynomial.evalRingHom x)).eval (ξ k1 x) := by
                intro x hx
                rw [eval_remY, map_eval_derivative, hk1_root x hx]
                simpa using hb_pos_on_k1 x hx (ξ k1 x) (hmono x hx hk1_gt) le_rfl
              have hrb_ne : remY b ≠ 0 := by
                obtain ⟨x₀, hx₀⟩ := hU_conn.nonempty
                intro h0
                have := hrb_pos_k1 x₀ hx₀
                rw [h0, Polynomial.map_zero, Polynomial.eval_zero] at this
                exact lt_irrefl 0 this
              have hrb_B : remY b ∈ B := hB_rem b hb hb_deg_pos hrb_ne
              obtain ⟨cb', hcb'_SI, hcb'_eq⟩ := ih_deg b.derivative hb'_B hb'_deg k1 hk1_root
              -- Find smallest k2 > k1 where remY b vanishes on ξ k2 (if any)
              let remSet : Finset (Fin s) :=
                Finset.univ.filter fun j => k1 < j ∧
                  ∀ x ∈ U, ((remY b).map (Polynomial.evalRingHom x)).eval (ξ j x) = 0
              have hcr_ex : ∃ cr : (Fin 2 → ℝ) → ℝ, SI cr ∧
                  (∀ x ∈ U, ∀ y : ℝ, y ≤ ξ k1 x → cr (fun i => if i = 0 then x else y) = 0) ∧
                  (∀ x ∈ U, ∀ y : ℝ, ξ k1 x < y →
                    (cr (fun i => if i = 0 then x else y) = 0 ∧
                      0 < ((remY b).map (Polynomial.evalRingHom x)).eval y) ∨
                    cr (fun i => if i = 0 then x else y) =
                      ((remY b).map (Polynomial.evalRingHom x)).eval y) := by
                by_cases hrne : remSet.Nonempty
                · let k2 : Fin s := remSet.min' hrne
                  have hk2_mem : k2 ∈ remSet := Finset.min'_mem remSet hrne
                  have hk2_gt : k1 < k2 := (Finset.mem_filter.mp hk2_mem).2.1
                  have hk2_root : ∀ x ∈ U, ((remY b).map (Polynomial.evalRingHom x)).eval (ξ k2 x) = 0 :=
                    (Finset.mem_filter.mp hk2_mem).2.2
                  obtain ⟨cr, hcr_SI, hcr_eq⟩ := ih_deg (remY b) hrb_B hrb_deg k2 hk2_root
                  refine ⟨cr, hcr_SI, ?_, ?_⟩
                  · intro x hx y hy
                    rw [hcr_eq x hx y, if_neg (not_lt.mpr (hy.trans (hmono x hx hk2_gt).le))]
                  · intro x hx y hy
                    rw [hcr_eq x hx y]
                    by_cases hy2 : ξ k2 x < y
                    · right; exact if_pos hy2
                    · rcases eq_or_lt_of_le (not_lt.mp hy2) with rfl | hlt2
                      · right; rw [if_neg hy2, hk2_root x hx]
                      · left
                        refine ⟨if_neg hy2, ?_⟩
                        have hr_no : ∀ z, ξ k1 x < z → z < ξ k2 x →
                            ((remY b).map (Polynomial.evalRingHom x)).eval z ≠ 0 := by
                          intro z hz1 hz2 hz0
                          obtain ⟨j, rfl⟩ := hroots (remY b) hrb_B x hx z hz0
                          have hj1 : k1 < j := (hmono x hx).lt_iff_lt.mp hz1
                          have hj2 : j < k2 := (hmono x hx).lt_iff_lt.mp hz2
                          have hj_all : ∀ x' ∈ U, ((remY b).map (Polynomial.evalRingHom x')).eval (ξ j x') = 0 := by
                            rcases hdich (remY b) hrb_B j with h | h
                            · exact h
                            · exact False.elim (h x hx hz0)
                          have hj_in : j ∈ remSet := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj1, hj_all⟩
                          exact not_le.mpr hj2 (Finset.min'_le remSet j hj_in)
                        exact poly_pos_of_pos_no_root (hrb_pos_k1 x hx) hr_no y hy.le hlt2
                · rw [Finset.not_nonempty_iff_eq_empty] at hrne
                  refine ⟨fun _ => 0, by simpa using SI_poly 0, fun _ _ _ _ => rfl, ?_⟩
                  intro x hx y hy
                  left
                  refine ⟨rfl, ?_⟩
                  have hr_no : ∀ z, ξ k1 x < z → z < y + 1 →
                      ((remY b).map (Polynomial.evalRingHom x)).eval z ≠ 0 := by
                    intro z hz1 _ hz0
                    obtain ⟨j, rfl⟩ := hroots (remY b) hrb_B x hx z hz0
                    have hj1 : k1 < j := (hmono x hx).lt_iff_lt.mp hz1
                    have hj_all : ∀ x' ∈ U, ((remY b).map (Polynomial.evalRingHom x')).eval (ξ j x') = 0 := by
                      rcases hdich (remY b) hrb_B j with h | h
                      · exact h
                      · exact False.elim (h x hx hz0)
                    have : j ∈ remSet := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj1, hj_all⟩
                    rw [hrne] at this; exact False.elim (Finset.notMem_empty j this)
                  exact poly_pos_of_pos_no_root (hrb_pos_k1 x hx) hr_no y hy.le (by linarith)
              -- Assemble g_fn and c = min (max 0 c_prev) (max b g_fn)
              obtain ⟨cr, hcr_SI, hcr_le, hcr_gt⟩ := hcr_ex
              let g_fn : (Fin 2 → ℝ) → ℝ := fun z =>
                MvPolynomial.eval z (MvPolynomial.C (1 / (b.natDegree : ℝ)) * MvPolynomial.X 1) * cb' z + cr z
              have hg_SI : SI g_fn := SI_add (SI_mul_poly _ hcb'_SI) hcr_SI
              let c : (Fin 2 → ℝ) → ℝ := fun z =>
                min (max 0 (c_prev z)) (max (MvPolynomial.eval z (fromPolyY b)) (g_fn z))
              have hc_SI : SI c :=
                SI_inf (SI_sup (by simpa using SI_poly 0) hc_prev_SI) (SI_sup (SI_poly _) hg_SI)
              refine ⟨c, hc_SI, fun x hx y => ?_⟩
              have hev_b : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y) (fromPolyY b) =
                  (b.map (Polynomial.evalRingHom x)).eval y := by simp [eval_fromPolyY]
              have hev_y : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y)
                  (MvPolynomial.C (1 / (b.natDegree : ℝ)) * MvPolynomial.X 1) =
                  (1 / (b.natDegree : ℝ)) * y := by simp
              dsimp only [c]
              rw [hev_b]
              by_cases hyk : ξ k x < y
              · rw [if_pos hyk, hc_prev_gt x hx y hyk]
                have hgle : g_fn (fun i => if i = 0 then x else y) ≤ (b.map (Polynomial.evalRingHom x)).eval y := by
                  dsimp only [g_fn]
                  rw [hev_y, hcb'_eq x hx y]
                  by_cases hy1 : ξ k1 x < y
                  · rw [if_pos hy1]
                    rcases hcr_gt x hx y hy1 with ⟨hcr0, hrb_pos⟩ | hcr_eq'
                    · rw [hcr0, add_zero]
                      have hrem := eval_remY b x y
                      rw [map_eval_derivative] at hrem
                      linarith
                    · rw [hcr_eq']
                      have hrem := eval_remY b x y
                      rw [map_eval_derivative] at hrem
                      linarith
                  · rw [if_neg hy1, mul_zero, zero_add, hcr_le x hx y (not_lt.mp hy1)]
                    exact (hb_pos_on_k1 x hx y hyk (not_lt.mp hy1)).le
                rw [max_eq_left hgle, min_eq_right (le_max_right _ _)]
              · rw [if_neg hyk]
                have hy1 : y ≤ ξ k1 x := (not_lt.mp hyk).trans (hmono x hx hk1_gt).le
                have hg0 : g_fn (fun i => if i = 0 then x else y) = 0 := by
                  dsimp only [g_fn]
                  rw [hev_y, hcb'_eq x hx y, if_neg (not_lt.mpr hy1), mul_zero, zero_add, hcr_le x hx y hy1]
                rw [hg0]
                by_cases hex : ∃ j : Fin s, j < k ∧ (b.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0 ∧ y ≤ ξ j x
                · rw [hc_prev_le x hx y hex, max_self, min_eq_left (le_max_right _ _)]
                · push Not at hex
                  rw [hc_prev_mid x hx y (not_lt.mp hyk) hex]
                  have hnp := hb_nonpos_mid x hx y (not_lt.mp hyk) hex
                  rw [max_eq_left hnp, max_eq_right hnp, min_self]
            · -- Subcase B1: no root of b' above ξ k
              rw [Finset.not_nonempty_iff_eq_empty] at hdne
              have hb_pos_gt : ∀ x ∈ U, ∀ y : ℝ, ξ k x < y →
                  0 < (b.map (Polynomial.evalRingHom x)).eval y := by
                intro x hx y hy
                have hb'_no : ∀ z, ξ k x < z → z < y + 1 →
                    (b.derivative.map (Polynomial.evalRingHom x)).eval z ≠ 0 := by
                  intro z hz1 _ hz0
                  obtain ⟨j, rfl⟩ := hroots b.derivative hb'_B x hx z hz0
                  have hkj : k < j := (hmono x hx).lt_iff_lt.mp hz1
                  have hj_all : ∀ x' ∈ U, (b.derivative.map (Polynomial.evalRingHom x')).eval (ξ j x') = 0 := by
                    rcases hdich b.derivative hb'_B j with h | h
                    · exact h
                    · exact False.elim (h x hx hz0)
                  have : j ∈ derSet := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hkj, hj_all⟩
                  rw [hdne] at this; exact False.elim (Finset.notMem_empty j this)
                have hmono_b : StrictMonoOn (fun z => (b.map (Polynomial.evalRingHom x)).eval z)
                    (Set.Icc (ξ k x) y) := by
                  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
                  · exact (b.map (Polynomial.evalRingHom x)).continuous.continuousOn
                  · intro z hz
                    rw [interior_Icc] at hz
                    rw [(Polynomial.hasDerivAt _ z).deriv, map_eval_derivative]
                    exact poly_pos_of_pos_no_root (hb'_pos x hx) hb'_no z hz.1.le (by linarith [hz.2])
                have hlt := hmono_b (a := ξ k x) (b := y) ⟨le_rfl, hy.le⟩ ⟨hy.le, le_rfl⟩ hy
                dsimp only at hlt
                rwa [hb_root x hx] at hlt
              let c : (Fin 2 → ℝ) → ℝ := fun z =>
                min (max 0 (c_prev z)) (max 0 (MvPolynomial.eval z (fromPolyY b)))
              have hc_SI : SI c :=
                SI_inf (SI_sup (by simpa using SI_poly 0) hc_prev_SI)
                       (SI_sup (by simpa using SI_poly 0) (SI_poly _))
              refine ⟨c, hc_SI, fun x hx y => ?_⟩
              have hev_b : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y) (fromPolyY b) =
                  (b.map (Polynomial.evalRingHom x)).eval y := by simp [eval_fromPolyY]
              dsimp only [c]
              rw [hev_b]
              by_cases hyk : ξ k x < y
              · rw [if_pos hyk, hc_prev_gt x hx y hyk]
                have hpos := (hb_pos_gt x hx y hyk).le
                rw [max_eq_right hpos, min_self]
              · rw [if_neg hyk]
                by_cases hex : ∃ j : Fin s, j < k ∧ (b.map (Polynomial.evalRingHom x)).eval (ξ j x) = 0 ∧ y ≤ ξ j x
                · rw [hc_prev_le x hx y hex, max_self, min_eq_left (le_max_left _ _)]
                · push Not at hex
                  rw [hc_prev_mid x hx y (not_lt.mp hyk) hex]
                  have hnp := hb_nonpos_mid x hx y (not_lt.mp hyk) hex
                  rw [max_eq_left hnp, min_self]
          -- Apply hpos_case to a or -a!
          obtain ⟨c_prev, hc_prev_SI, hc_prev_gt, hc_prev_mid, hc_prev_le⟩ := hprev
          rcases ha'_sign with hpos | hneg
          · exact hpos_case a ha hdeg_eq hk hpos c_prev hc_prev_SI hc_prev_gt hc_prev_mid hc_prev_le
          · have hna_B : -a ∈ B := hB_neg a ha
            have hna_deg : (-a).natDegree = d + 1 := by rw [Polynomial.natDegree_neg]; exact hdeg_eq
            have hna_root : ∀ x ∈ U, ((-a).map (Polynomial.evalRingHom x)).eval (ξ k x) = 0 := by
              intro x hx; rw [Polynomial.map_neg, Polynomial.eval_neg, hk x hx, neg_zero]
            have hna'_pos : ∀ x ∈ U, 0 < ((-a).derivative.map (Polynomial.evalRingHom x)).eval (ξ k x) := by
              intro x hx; simp only [Polynomial.derivative_neg, Polynomial.map_neg, Polynomial.eval_neg]
              linarith [hneg x hx]
            obtain ⟨cn, hcn_SI, hcn_eq⟩ := hpos_case (-a) hna_B hna_deg hna_root hna'_pos
              (fun z => -c_prev z) (SI_neg hc_prev_SI)
              (fun x hx y hy => by simp [hc_prev_gt x hx y hy])
              (fun x hx y hy hgt => by
                simp [hc_prev_mid x hx y hy (fun j hjk hj0 => hgt j hjk (by simp [hj0]))])
              (fun x hx y ⟨j, hjk, hj0, hyj⟩ => by
                simp [hc_prev_le x hx y ⟨j, hjk, by simpa using hj0, hyj⟩])
            refine ⟨fun z => -cn z, SI_neg hcn_SI, fun x hx y => ?_⟩
            dsimp only
            rw [hcn_eq x hx y]
            split_ifs <;> simp

/- ## Part 6: Strip Representatives, Diagonal-Strip Separator, and Main Theorem -/

lemma continuous_of_piecewise {ι : Type} [Finite ι] {f : (Fin 2 → ℝ) → ℝ}
    {P : ι → Set (Fin 2 → ℝ)} {g : ι → MvPolynomial (Fin 2) ℝ}
    (hcl : ∀ i, IsClosed (P i)) (hcov : (⋃ i, P i) = Set.univ)
    (heq : ∀ i, ∀ x ∈ P i, f x = MvPolynomial.eval x (g i)) :
    Continuous f := by
  rw [continuous_iff_isClosed]
  intro S hS
  have hpre : f ⁻¹' S = ⋃ i, (P i ∩ (fun x => MvPolynomial.eval x (g i)) ⁻¹' S) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      have hx_cov : x ∈ ⋃ i, P i := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx_cov
      exact ⟨i, hi, by rw [← heq i x hi]; exact hx⟩
    · rintro ⟨i, hi, hgi⟩
      rw [heq i x hi]; exact hgi
  rw [hpre]
  exact isClosed_iUnion_of_finite fun i => (hcl i).inter (hS.preimage (MvPolynomial.continuous_eval _))

lemma const_piece_on_connected {ι : Type} [Finite ι] {f : (Fin 2 → ℝ) → ℝ}
    (hf : Continuous f) {g : ι → MvPolynomial (Fin 2) ℝ}
    (hval : ∀ x, ∃ i, f x = MvPolynomial.eval x (g i))
    {D : Set (Fin 2 → ℝ)} (hD_conn : IsConnected D)
    (hsep : ∀ i j, g i ≠ g j → ∀ x ∈ D, MvPolynomial.eval x (g i) ≠ MvPolynomial.eval x (g j)) :
    ∃ i : ι, ∀ x ∈ D, f x = MvPolynomial.eval x (g i) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hD_conn.nonempty
  obtain ⟨i₀, hi₀⟩ := hval x₀
  refine ⟨i₀, ?_⟩
  let Z : Set (Fin 2 → ℝ) := {x | f x = MvPolynomial.eval x (g i₀)}
  let NZ : Set (Fin 2 → ℝ) := ⋃ j : {j : ι // g j ≠ g i₀}, {x | f x = MvPolynomial.eval x (g j.1)}
  have hZ_closed : IsClosed Z := isClosed_eq hf (MvPolynomial.continuous_eval _)
  have hNZ_closed : IsClosed NZ :=
    isClosed_iUnion_of_finite fun j => isClosed_eq hf (MvPolynomial.continuous_eval _)
  have hpart : ∀ x ∈ D, x ∈ Z ↔ x ∉ NZ := by
    intro x hx
    constructor
    · intro hxZ hxNZ
      obtain ⟨⟨j, hj⟩, hxj⟩ := Set.mem_iUnion.mp hxNZ
      exact hsep j i₀ hj x hx (hxj.symm.trans hxZ)
    · intro hxNZ
      obtain ⟨j, hxj⟩ := hval x
      by_cases hji : g j = g i₀
      · change f x = MvPolynomial.eval x (g i₀)
        rw [← hji]; exact hxj
      · exact False.elim (hxNZ (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩))
  have hZ_clopen : IsClopen (Subtype.val ⁻¹' Z : Set D) := by
    refine ⟨hZ_closed.preimage continuous_subtype_val, ?_⟩
    have : (Subtype.val ⁻¹' Z : Set D) = (Subtype.val ⁻¹' NZ : Set D)ᶜ := by
      ext ⟨x, hx⟩; exact hpart x hx
    rw [this]
    exact (hNZ_closed.preimage continuous_subtype_val).isOpen_compl
  have : ConnectedSpace D := Subtype.connectedSpace hD_conn
  rcases isClopen_iff.mp hZ_clopen with hemp | huniv
  · have hmem : (⟨x₀, hx₀⟩ : D) ∈ (Subtype.val ⁻¹' Z : Set D) := hi₀
    rw [hemp] at hmem
    exact False.elim hmem
  · intro x hx
    have hmem : (⟨x, hx⟩ : D) ∈ (Subtype.val ⁻¹' Z : Set D) := by rw [huniv]; trivial
    exact hmem

/-- Open connected intervals complementary to a finite set `Crit : Finset ℝ`. -/
def critInterval (Crit : Finset ℝ) (p : Fin (Crit.card + 1)) : Set ℝ :=
  let emb := Crit.orderEmbOfFin rfl
  {x : ℝ | (∀ h : 0 < p.val, emb ⟨p.val - 1, by omega⟩ < x) ∧
           (∀ h : p.val < Crit.card, x < emb ⟨p.val, h⟩)}

lemma critInterval_open (Crit : Finset ℝ) (p : Fin (Crit.card + 1)) :
    IsOpen (critInterval Crit p) := by
  dsimp only [critInterval]
  have h1 : IsOpen {x : ℝ | ∀ h : 0 < p.val, Crit.orderEmbOfFin rfl ⟨p.val - 1, by omega⟩ < x} := by
    by_cases hp : 0 < p.val
    · have : {x : ℝ | ∀ h : 0 < p.val, Crit.orderEmbOfFin rfl ⟨p.val - 1, by omega⟩ < x} =
          Set.Ioi (Crit.orderEmbOfFin rfl ⟨p.val - 1, by omega⟩) := by
        ext x; simp [hp]
      rw [this]; exact isOpen_Ioi
    · have : {x : ℝ | ∀ h : 0 < p.val, Crit.orderEmbOfFin rfl ⟨p.val - 1, by omega⟩ < x} = Set.univ := by
        ext x; simp [hp]
      rw [this]; exact isOpen_univ
  have h2 : IsOpen {x : ℝ | ∀ h : p.val < Crit.card, x < Crit.orderEmbOfFin rfl ⟨p.val, h⟩} := by
    by_cases hp : p.val < Crit.card
    · have : {x : ℝ | ∀ h : p.val < Crit.card, x < Crit.orderEmbOfFin rfl ⟨p.val, h⟩} =
          Set.Iio (Crit.orderEmbOfFin rfl ⟨p.val, hp⟩) := by
        ext x; simp [hp]
      rw [this]; exact isOpen_Iio
    · have : {x : ℝ | ∀ h : p.val < Crit.card, x < Crit.orderEmbOfFin rfl ⟨p.val, h⟩} = Set.univ := by
        ext x; simp [hp]
      rw [this]; exact isOpen_univ
  exact h1.inter h2

lemma critInterval_connected (Crit : Finset ℝ) (p : Fin (Crit.card + 1)) :
    IsConnected (critInterval Crit p) := by
  let emb := Crit.orderEmbOfFin rfl
  have hconv : Convex ℝ (critInterval Crit p) := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hx1 : emb ⟨p.val - 1, by omega⟩ < x := hx.1 h
      have hy1 : emb ⟨p.val - 1, by omega⟩ < y := hy.1 h
      change emb ⟨p.val - 1, by omega⟩ < a * x + b * y
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        rw [hb1]; linarith
      · have h1 := mul_lt_mul_of_pos_left hx1 ha'
        have h2 := mul_le_mul_of_nonneg_left hy1.le hb
        have h3 : emb ⟨p.val - 1, by omega⟩ = a * emb ⟨p.val - 1, by omega⟩ + b * emb ⟨p.val - 1, by omega⟩ := by
          linear_combination -emb ⟨p.val - 1, by omega⟩ * hab
        linarith
    · have hx2 : x < emb ⟨p.val, h⟩ := hx.2 h
      have hy2 : y < emb ⟨p.val, h⟩ := hy.2 h
      change a * x + b * y < emb ⟨p.val, h⟩
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        rw [hb1]; linarith
      · have h1 := mul_lt_mul_of_pos_left hx2 ha'
        have h2 := mul_le_mul_of_nonneg_left hy2.le hb
        have h3 : emb ⟨p.val, h⟩ = a * emb ⟨p.val, h⟩ + b * emb ⟨p.val, h⟩ := by
          linear_combination -emb ⟨p.val, h⟩ * hab
        linarith
  refine ⟨?_, hconv.isPreconnected⟩
  by_cases h0 : 0 < p.val
  · by_cases h1 : p.val < Crit.card
    · refine ⟨(emb ⟨p.val - 1, by omega⟩ + emb ⟨p.val, h1⟩) / 2, fun _ => ?_, fun _ => ?_⟩
      · have hlt : emb ⟨p.val - 1, by omega⟩ < emb ⟨p.val, h1⟩ := emb.strictMono (by show p.val - 1 < p.val; omega)
        change emb ⟨p.val - 1, by omega⟩ < _
        linarith
      · have hlt : emb ⟨p.val - 1, by omega⟩ < emb ⟨p.val, h1⟩ := emb.strictMono (by show p.val - 1 < p.val; omega)
        change _ < emb ⟨p.val, h1⟩
        linarith
    · exact ⟨emb ⟨p.val - 1, by omega⟩ + 1, fun _ => by change emb _ < _; linarith, fun h => False.elim (h1 h)⟩
  · by_cases h1 : p.val < Crit.card
    · exact ⟨emb ⟨p.val, h1⟩ - 1, fun h => False.elim (h0 h), fun _ => by change _ < emb _; linarith⟩
    · exact ⟨0, fun h => False.elim (h0 h), fun h => False.elim (h1 h)⟩

lemma critInterval_disj (Crit : Finset ℝ) (p : Fin (Crit.card + 1)) (x : ℝ)
    (hx : x ∈ critInterval Crit p) : x ∉ Crit := by
  intro hxC
  have hrange : x ∈ Set.range (Crit.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hxC
  obtain ⟨k, rfl⟩ := hrange
  by_cases hlt : k.val < p.val
  · have hpos : 0 < p.val := by omega
    have hle : k ≤ ⟨p.val - 1, by omega⟩ := by show k.val ≤ p.val - 1; omega
    have := (Crit.orderEmbOfFin rfl).monotone hle
    linarith [hx.1 hpos]
  · have hlt2 : p.val < Crit.card := by omega
    have hle : ⟨p.val, hlt2⟩ ≤ k := by show p.val ≤ k.val; omega
    have := (Crit.orderEmbOfFin rfl).monotone hle
    linarith [hx.2 hlt2]

lemma critInterval_cover (Crit : Finset ℝ) (x : ℝ) (hx : x ∉ Crit) :
    ∃ p : Fin (Crit.card + 1), x ∈ critInterval Crit p := by
  classical
  set emb := Crit.orderEmbOfFin rfl
  let S : Finset (Fin Crit.card) := Finset.univ.filter fun k => emb k < x
  by_cases hne : S.Nonempty
  · let k0 : Fin Crit.card := S.max' hne
    have hk0_mem : k0 ∈ S := Finset.max'_mem S hne
    have hk0_lt : emb k0 < x := (Finset.mem_filter.mp hk0_mem).2
    refine ⟨⟨k0.val + 1, by omega⟩, fun _ => ?_, fun h => ?_⟩
    · have heq : (⟨k0.val + 1 - 1, by omega⟩ : Fin Crit.card) = k0 := by ext; simp
      rw [heq]; exact hk0_lt
    · by_contra hle
      have hne_eq : emb ⟨k0.val + 1, h⟩ ≠ x := fun heq =>
        hx (heq ▸ Finset.orderEmbOfFin_mem Crit rfl _)
      have hlt' : emb ⟨k0.val + 1, h⟩ < x := lt_of_le_of_ne (not_lt.mp hle) hne_eq
      have hin : ⟨k0.val + 1, h⟩ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩
      have hle' : (⟨k0.val + 1, h⟩ : Fin Crit.card) ≤ k0 := Finset.le_max' S ⟨k0.val + 1, h⟩ hin
      have hle'' : k0.val + 1 ≤ k0.val := hle'
      omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨⟨0, by omega⟩, fun h => False.elim (Nat.not_lt_zero _ h), fun h => ?_⟩
    by_contra hle
    have hne_eq : emb ⟨0, h⟩ ≠ x := fun heq =>
      hx (heq ▸ Finset.orderEmbOfFin_mem Crit rfl _)
    have hlt' : emb ⟨0, h⟩ < x := lt_of_le_of_ne (not_lt.mp hle) hne_eq
    have : ⟨0, h⟩ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩
    rw [hne] at this; exact False.elim (Finset.notMem_empty _ this)

lemma critInterval_sep (Crit : Finset ℝ) {p₁ p₂ : Fin (Crit.card + 1)} (hlt : p₁ < p₂) :
    ∃ γ ∈ Crit, (∀ x ∈ critInterval Crit p₁, x < γ) ∧ (∀ x ∈ critInterval Crit p₂, γ < x) := by
  have hp1 : p₁.val < Crit.card := by omega
  have hp2 : 0 < p₂.val := by omega
  set emb := Crit.orderEmbOfFin rfl
  refine ⟨emb ⟨p₁.val, hp1⟩, Finset.orderEmbOfFin_mem Crit rfl _, ?_, ?_⟩
  · intro x hx; exact hx.2 hp1
  · intro x hx
    have hle : (⟨p₁.val, hp1⟩ : Fin Crit.card) ≤ ⟨p₂.val - 1, by omega⟩ := by
      show p₁.val ≤ p₂.val - 1; omega
    exact (emb.monotone hle).trans_lt (hx.1 hp2)

/-- Vertical open cell between consecutive root curves `ξ` over `U`. -/
def vertCell {s : ℕ} (U : Set ℝ) (ξ : Fin s → ℝ → ℝ) (k : Fin (s + 1)) : Set (Fin 2 → ℝ) :=
  {z | z 0 ∈ U ∧
       (∀ h : 0 < k.val, ξ ⟨k.val - 1, by omega⟩ (z 0) < z 1) ∧
       (∀ h : k.val < s, z 1 < ξ ⟨k.val, h⟩ (z 0))}

lemma vertCell_open {s : ℕ} {U : Set ℝ} (hU : IsOpen U) {ξ : Fin s → ℝ → ℝ}
    (hcont : ∀ k : Fin s, ContinuousOn (ξ k) U) (k : Fin (s + 1)) :
    IsOpen (vertCell U ξ k) := by
  rw [Metric.isOpen_iff]
  intro z ⟨hzU, hzL, hzR⟩
  obtain ⟨δU, hδU_pos, hδU⟩ := Metric.isOpen_iff.mp hU (z 0) hzU
  have hL : ∃ δL > (0 : ℝ), ∀ w : Fin 2 → ℝ, dist w z < δL → w 0 ∈ U →
      ∀ h : 0 < k.val, ξ ⟨k.val - 1, by omega⟩ (w 0) < w 1 := by
    by_cases hk : 0 < k.val
    · set j : Fin s := ⟨k.val - 1, by omega⟩
      have hgap : 0 < z 1 - ξ j (z 0) := sub_pos.mpr (hzL hk)
      obtain ⟨δ1, hδ1_pos, hδ1⟩ := Metric.continuousOn_iff.mp (hcont j) (z 0) hzU
        ((z 1 - ξ j (z 0)) / 3) (by linarith)
      refine ⟨min δ1 ((z 1 - ξ j (z 0)) / 3), lt_min hδ1_pos (by linarith), fun w hw hwU _ => ?_⟩
      have hw0 : dist (w 0) (z 0) < δ1 := (dist_le_pi_dist w z 0).trans_lt (hw.trans_le (min_le_left _ _))
      have hw1 : |w 1 - z 1| < (z 1 - ξ j (z 0)) / 3 := by
        simpa [Real.dist_eq] using (dist_le_pi_dist w z 1).trans_lt (hw.trans_le (min_le_right _ _))
      have hξ := hδ1 (w 0) hwU hw0
      rw [Real.dist_eq, abs_lt] at hξ
      rw [abs_lt] at hw1
      linarith
    · exact ⟨1, zero_lt_one, fun _ _ _ h => False.elim (hk h)⟩
  have hR : ∃ δR > (0 : ℝ), ∀ w : Fin 2 → ℝ, dist w z < δR → w 0 ∈ U →
      ∀ h : k.val < s, w 1 < ξ ⟨k.val, h⟩ (w 0) := by
    by_cases hk : k.val < s
    · set j : Fin s := ⟨k.val, hk⟩
      have hgap : 0 < ξ j (z 0) - z 1 := sub_pos.mpr (hzR hk)
      obtain ⟨δ1, hδ1_pos, hδ1⟩ := Metric.continuousOn_iff.mp (hcont j) (z 0) hzU
        ((ξ j (z 0) - z 1) / 3) (by linarith)
      refine ⟨min δ1 ((ξ j (z 0) - z 1) / 3), lt_min hδ1_pos (by linarith), fun w hw hwU _ => ?_⟩
      have hw0 : dist (w 0) (z 0) < δ1 := (dist_le_pi_dist w z 0).trans_lt (hw.trans_le (min_le_left _ _))
      have hw1 : |w 1 - z 1| < (ξ j (z 0) - z 1) / 3 := by
        simpa [Real.dist_eq] using (dist_le_pi_dist w z 1).trans_lt (hw.trans_le (min_le_right _ _))
      have hξ := hδ1 (w 0) hwU hw0
      rw [Real.dist_eq, abs_lt] at hξ
      rw [abs_lt] at hw1
      linarith
    · exact ⟨1, zero_lt_one, fun _ _ _ h => False.elim (hk h)⟩
  obtain ⟨δL, hδL_pos, hδL⟩ := hL
  obtain ⟨δR, hδR_pos, hδR⟩ := hR
  refine ⟨min δU (min δL δR), lt_min hδU_pos (lt_min hδL_pos hδR_pos), fun w hw => ?_⟩
  have hwU : w 0 ∈ U := hδU ((dist_le_pi_dist w z 0).trans_lt (hw.trans_le (min_le_left _ _)))
  exact ⟨hwU, hδL w (hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hwU,
    hδR w (hw.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hwU⟩

lemma vertCell_connected {s : ℕ} {U : Set ℝ} (hU_conn : IsConnected U) {ξ : Fin s → ℝ → ℝ}
    (hmono : ∀ x ∈ U, StrictMono (fun k => ξ k x))
    (hcont : ∀ k : Fin s, ContinuousOn (ξ k) U) (k : Fin (s + 1)) :
    IsConnected (vertCell U ξ k) := by
  by_cases h0 : 0 < k.val
  · by_cases h1 : k.val < s
    · -- Bounded strip between ξ (k-1) and ξ k: image of U × (0, 1)
      set jL : Fin s := ⟨k.val - 1, by omega⟩
      set jR : Fin s := ⟨k.val, h1⟩
      let φ : ℝ × ℝ → (Fin 2 → ℝ) := fun p i =>
        if i = 0 then p.1 else (1 - p.2) * ξ jL p.1 + p.2 * ξ jR p.1
      have hφ_cont : ContinuousOn φ (U ×ˢ Set.Ioo (0 : ℝ) 1) := by
        apply continuousOn_pi.mpr
        intro i
        fin_cases i
        · exact continuousOn_fst
        · exact ((continuousOn_const.sub continuousOn_snd).mul
            ((hcont jL).comp continuousOn_fst (fun p hp => hp.1))).add
            (continuousOn_snd.mul ((hcont jR).comp continuousOn_fst (fun p hp => hp.1)))
      have hφ_img : φ '' (U ×ˢ Set.Ioo (0 : ℝ) 1) = vertCell U ξ k := by
        ext z
        constructor
        · rintro ⟨⟨x, t⟩, ⟨hxU, ht0, ht1⟩, rfl⟩
          have hlt : ξ jL x < ξ jR x := hmono x hxU (by show k.val - 1 < k.val; omega)
          refine ⟨hxU, fun _ => ?_, fun _ => ?_⟩
          · change ξ jL x < (1 - t) * ξ jL x + t * ξ jR x; nlinarith
          · change (1 - t) * ξ jL x + t * ξ jR x < ξ jR x; nlinarith
        · rintro ⟨hzU, hzL, hzR⟩
          have hltL := hzL h0
          have hltR := hzR h1
          have hgap : 0 < ξ jR (z 0) - ξ jL (z 0) := by linarith
          refine ⟨(z 0, (z 1 - ξ jL (z 0)) / (ξ jR (z 0) - ξ jL (z 0))),
            ⟨hzU, div_pos (by linarith) hgap, (div_lt_one hgap).mpr (by linarith)⟩, ?_⟩
          ext i
          fin_cases i
          · rfl
          · change (1 - (z 1 - ξ jL (z 0)) / (ξ jR (z 0) - ξ jL (z 0))) * ξ jL (z 0) +
              (z 1 - ξ jL (z 0)) / (ξ jR (z 0) - ξ jL (z 0)) * ξ jR (z 0) = z 1
            field_simp [hgap.ne']; ring
      rw [← hφ_img]
      exact (hU_conn.prod (isConnected_Ioo zero_lt_one)).image _ hφ_cont
    · -- Top unbounded strip above ξ (k-1): image of U × (0, ∞)
      set jL : Fin s := ⟨k.val - 1, by omega⟩
      let φ : ℝ × ℝ → (Fin 2 → ℝ) := fun p i => if i = 0 then p.1 else ξ jL p.1 + p.2
      have hφ_cont : ContinuousOn φ (U ×ˢ Set.Ioi (0 : ℝ)) := by
        apply continuousOn_pi.mpr
        intro i
        fin_cases i
        · exact continuousOn_fst
        · exact ((hcont jL).comp continuousOn_fst (fun p hp => hp.1)).add continuousOn_snd
      have hφ_img : φ '' (U ×ˢ Set.Ioi (0 : ℝ)) = vertCell U ξ k := by
        ext z
        constructor
        · rintro ⟨⟨x, t⟩, ⟨hxU, ht0⟩, rfl⟩
          refine ⟨hxU, fun _ => ?_, fun h => False.elim (h1 h)⟩
          change ξ jL x < ξ jL x + t
          have : (0 : ℝ) < t := ht0
          linarith
        · rintro ⟨hzU, hzL, _⟩
          refine ⟨(z 0, z 1 - ξ jL (z 0)), ⟨hzU, sub_pos.mpr (hzL h0)⟩, ?_⟩
          ext i; fin_cases i <;> simp [φ]
      rw [← hφ_img]
      exact (hU_conn.prod isConnected_Ioi).image _ hφ_cont
  · by_cases h1 : k.val < s
    · -- Bottom unbounded strip below ξ k: image of U × (0, ∞)
      set jR : Fin s := ⟨k.val, h1⟩
      let φ : ℝ × ℝ → (Fin 2 → ℝ) := fun p i => if i = 0 then p.1 else ξ jR p.1 - p.2
      have hφ_cont : ContinuousOn φ (U ×ˢ Set.Ioi (0 : ℝ)) := by
        apply continuousOn_pi.mpr
        intro i
        fin_cases i
        · exact continuousOn_fst
        · exact ((hcont jR).comp continuousOn_fst (fun p hp => hp.1)).sub continuousOn_snd
      have hφ_img : φ '' (U ×ˢ Set.Ioi (0 : ℝ)) = vertCell U ξ k := by
        ext z
        constructor
        · rintro ⟨⟨x, t⟩, ⟨hxU, ht0⟩, rfl⟩
          refine ⟨hxU, fun h => False.elim (h0 h), fun _ => ?_⟩
          change ξ jR x - t < ξ jR x
          have : (0 : ℝ) < t := ht0
          linarith
        · rintro ⟨hzU, _, hzR⟩
          refine ⟨(z 0, ξ jR (z 0) - z 1), ⟨hzU, sub_pos.mpr (hzR h1)⟩, ?_⟩
          ext i; fin_cases i <;> simp [φ]
      rw [← hφ_img]
      exact (hU_conn.prod isConnected_Ioi).image _ hφ_cont
    · -- Whole vertical strip U × ℝ: image of U × univ
      let φ : ℝ × ℝ → (Fin 2 → ℝ) := fun p i => if i = 0 then p.1 else p.2
      have hφ_cont : ContinuousOn φ (U ×ˢ Set.univ) := by
        apply continuousOn_pi.mpr
        intro i; fin_cases i
        · exact continuousOn_fst
        · exact continuousOn_snd
      have hφ_img : φ '' (U ×ˢ Set.univ) = vertCell U ξ k := by
        ext z
        constructor
        · rintro ⟨⟨x, t⟩, ⟨hxU, _⟩, rfl⟩
          exact ⟨hxU, fun h => False.elim (h0 h), fun h => False.elim (h1 h)⟩
        · rintro ⟨hzU, _, _⟩
          refine ⟨(z 0, z 1), ⟨hzU, trivial⟩, ?_⟩
          ext i; fin_cases i <;> simp [φ]
      rw [← hφ_img]
      exact (hU_conn.prod isConnected_univ).image _ hφ_cont

lemma vertical_strip_SI {ι : Type} [Finite ι] {f : (Fin 2 → ℝ) → ℝ}
    (hf : Continuous f) {g : ι → MvPolynomial (Fin 2) ℝ}
    (hval : ∀ x, ∃ i, f x = MvPolynomial.eval x (g i))
    (B : Finset (Polynomial (Polynomial ℝ)))
    (hB_diff : ∀ i j, g i ≠ g j → toPolyY (g i - g j) ∈ B)
    (hB_neg : ∀ a ∈ B, -a ∈ B)
    (hB_der : ∀ a ∈ B, a.derivative ≠ 0 → a.derivative ∈ B)
    (hB_rem : ∀ a ∈ B, 0 < a.natDegree → remY a ≠ 0 → remY a ∈ B)
    {U : Set ℝ} (hU_open : IsOpen U) (hU_conn : IsConnected U)
    {s : ℕ} {ξ : Fin s → ℝ → ℝ}
    (hmono : ∀ x ∈ U, StrictMono (fun k => ξ k x))
    (hcont : ∀ k : Fin s, ContinuousOn (ξ k) U)
    (hroots : ∀ a ∈ B, ∀ x ∈ U, ∀ y : ℝ,
      (a.map (Polynomial.evalRingHom x)).eval y = 0 → ∃ k : Fin s, y = ξ k x)
    (hdich : ∀ a ∈ B, ∀ k : Fin s,
      (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0) ∨
      (∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ k x) ≠ 0)) :
    ∃ d : (Fin 2 → ℝ) → ℝ, SI d ∧
      ∀ x ∈ U, ∀ y : ℝ,
        d (fun i => if i = 0 then x else y) = f (fun i => if i = 0 then x else y) := by
  classical
  -- On each vertical cell vertCell U ξ k, f equals a single g (μ k).
  have hcell_piece : ∀ k : Fin (s + 1), ∃ i : ι, ∀ z ∈ vertCell U ξ k, f z = MvPolynomial.eval z (g i) := by
    intro k
    apply const_piece_on_connected hf hval (vertCell_connected hU_conn hmono hcont k)
    intro i j hij z ⟨hzU, hzL, hzR⟩ heq
    have h0 : ((toPolyY (g i - g j)).map (Polynomial.evalRingHom (z 0))).eval (z 1) = 0 := by
      rw [eval_toPolyY, map_sub, heq, sub_self]
    obtain ⟨m, hm⟩ := hroots (toPolyY (g i - g j)) (hB_diff i j hij) (z 0) hzU (z 1) h0
    by_cases hmk : m.val < k.val
    · have hpos : 0 < k.val := by omega
      have hle : m ≤ ⟨k.val - 1, by omega⟩ := by show m.val ≤ k.val - 1; omega
      linarith [hzL hpos, (hmono (z 0) hzU).monotone hle, hm]
    · have hlt : k.val < s := by omega
      have hle : ⟨k.val, hlt⟩ ≤ m := by show k.val ≤ m.val; omega
      linarith [hzR hlt, (hmono (z 0) hzU).monotone hle, hm]
  choose μ hμ using hcell_piece
  -- For each k : Fin s, build c k ∈ SI equal to g (μ k.succ) - g (μ k.castSucc) above ξ k and 0 below.
  have hstep : ∀ k : Fin s, ∃ c : (Fin 2 → ℝ) → ℝ, SI c ∧
      ∀ x ∈ U, ∀ y : ℝ, c (fun i => if i = 0 then x else y) =
        if ξ k x < y then MvPolynomial.eval (fun i => if i = 0 then x else y) (g (μ k.succ) - g (μ k.castSucc))
        else 0 := by
    intro k
    by_cases heq : g (μ k.succ) = g (μ k.castSucc)
    · refine ⟨fun _ => 0, by simpa using SI_poly 0, fun x _ y => ?_⟩
      simp [heq]
    · set a := toPolyY (g (μ k.succ) - g (μ k.castSucc))
      have haB : a ∈ B := hB_diff _ _ heq
      -- Continuity of f forces a(x, ξ k x) = 0 for all x ∈ U.
      have ha_root : ∀ x ∈ U, (a.map (Polynomial.evalRingHom x)).eval (ξ k x) = 0 := by
        intro x hx
        have h1 : ∀ ε > (0 : ℝ), ∃ y1, |y1 - ξ k x| < ε ∧
            f (fun i => if i = 0 then x else y1) =
              MvPolynomial.eval (fun i => if i = 0 then x else y1) (g (μ k.castSucc)) := by
          intro ε hε
          let lo : ℝ := if h : 0 < k.val then ξ ⟨k.val - 1, by omega⟩ x else ξ k x - 1
          have hlo : lo < ξ k x := by
            dsimp only [lo]
            split_ifs with h
            · exact hmono x hx (by show k.val - 1 < k.val; omega)
            · linarith
          let y1 := max (ξ k x - ε / 2) ((lo + ξ k x) / 2)
          refine ⟨y1, ?_, hμ k.castSucc _ ⟨hx, fun h => ?_, fun _ => ?_⟩⟩
          · rw [abs_lt]; constructor
            · have : ξ k x - ε / 2 ≤ y1 := le_max_left _ _; linarith
            · have : y1 < ξ k x := max_lt (by linarith) (by linarith); linarith
          · dsimp only [Fin.val_castSucc] at h ⊢
            change ξ ⟨k.val - 1, by omega⟩ x < y1
            have hlo_eq : lo = ξ ⟨k.val - 1, by omega⟩ x := dif_pos h
            have : (lo + ξ k x) / 2 ≤ y1 := le_max_right _ _
            linarith
          · change y1 < ξ k x
            exact max_lt (by linarith) (by linarith)
        have h2 : ∀ ε > (0 : ℝ), ∃ y2, |y2 - ξ k x| < ε ∧
            f (fun i => if i = 0 then x else y2) =
              MvPolynomial.eval (fun i => if i = 0 then x else y2) (g (μ k.succ)) := by
          intro ε hε
          let hi : ℝ := if h : k.val + 1 < s then ξ ⟨k.val + 1, h⟩ x else ξ k x + 1
          have hhi : ξ k x < hi := by
            dsimp only [hi]
            split_ifs with h
            · exact hmono x hx (by show k.val < k.val + 1; omega)
            · linarith
          let y2 := min (ξ k x + ε / 2) ((ξ k x + hi) / 2)
          refine ⟨y2, ?_, hμ k.succ _ ⟨hx, fun _ => ?_, fun h => ?_⟩⟩
          · rw [abs_lt]; constructor
            · have : ξ k x < y2 := lt_min (by linarith) (by linarith); linarith
            · have : y2 ≤ ξ k x + ε / 2 := min_le_left _ _; linarith
          · change ξ k x < y2
            exact lt_min (by linarith) (by linarith)
          · dsimp only [Fin.val_succ] at h ⊢
            change y2 < ξ ⟨k.val + 1, h⟩ x
            have hhi_eq : hi = ξ ⟨k.val + 1, h⟩ x := dif_pos h
            have : y2 ≤ (ξ k x + hi) / 2 := min_le_right _ _
            linarith
        -- By continuity of f and g at (x, ξ k x), f = g (μ k.castSucc) = g (μ k.succ) at (x, ξ k x).
        let z0 : Fin 2 → ℝ := fun i => if i = 0 then x else ξ k x
        have heq1 : f z0 = MvPolynomial.eval z0 (g (μ k.castSucc)) := by
          by_contra hne
          let δ := |f z0 - MvPolynomial.eval z0 (g (μ k.castSucc))| / 2
          have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hne))
          have hcont_diff : Continuous (fun y => f (fun i => if i = 0 then x else y) -
              MvPolynomial.eval (fun i => if i = 0 then x else y) (g (μ k.castSucc))) :=
            (hf.comp (continuous_pi fun i => by fin_cases i <;> [exact continuous_const; exact continuous_id])).sub
              ((MvPolynomial.continuous_eval _).comp
                (continuous_pi fun i => by fin_cases i <;> [exact continuous_const; exact continuous_id]))
          obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp hcont_diff.continuousAt δ hδ
          obtain ⟨y1, hy1, hy1_eq⟩ := h1 ε hε
          have hlt := hball (by simpa [Real.dist_eq] using hy1)
          rw [Real.dist_eq, hy1_eq, sub_self, zero_sub, abs_neg] at hlt
          change |f z0 - MvPolynomial.eval z0 (g (μ k.castSucc))| <
            |f z0 - MvPolynomial.eval z0 (g (μ k.castSucc))| / 2 at hlt
          linarith [abs_nonneg (f z0 - MvPolynomial.eval z0 (g (μ k.castSucc)))]
        have heq2 : f z0 = MvPolynomial.eval z0 (g (μ k.succ)) := by
          by_contra hne
          let δ := |f z0 - MvPolynomial.eval z0 (g (μ k.succ))| / 2
          have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hne))
          have hcont_diff : Continuous (fun y => f (fun i => if i = 0 then x else y) -
              MvPolynomial.eval (fun i => if i = 0 then x else y) (g (μ k.succ))) :=
            (hf.comp (continuous_pi fun i => by fin_cases i <;> [exact continuous_const; exact continuous_id])).sub
              ((MvPolynomial.continuous_eval _).comp
                (continuous_pi fun i => by fin_cases i <;> [exact continuous_const; exact continuous_id]))
          obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp hcont_diff.continuousAt δ hδ
          obtain ⟨y2, hy2, hy2_eq⟩ := h2 ε hε
          have hlt := hball (by simpa [Real.dist_eq] using hy2)
          rw [Real.dist_eq, hy2_eq, sub_self, zero_sub, abs_neg] at hlt
          change |f z0 - MvPolynomial.eval z0 (g (μ k.succ))| <
            |f z0 - MvPolynomial.eval z0 (g (μ k.succ))| / 2 at hlt
          linarith [abs_nonneg (f z0 - MvPolynomial.eval z0 (g (μ k.succ)))]
        have hev : ((a.map (Polynomial.evalRingHom x)).eval (ξ k x)) =
            MvPolynomial.eval z0 (g (μ k.succ) - g (μ k.castSucc)) := by
          simpa [a, z0] using eval_toPolyY (g (μ k.succ) - g (μ k.castSucc)) z0
        rw [hev, map_sub, ← heq1, ← heq2, sub_self]
      obtain ⟨c, hc_SI, hc_eq⟩ := mahe_truncation B hB_neg hB_der hB_rem hU_conn hmono hcont
        hroots hdich a.natDegree a haB le_rfl k ha_root
      refine ⟨c, hc_SI, fun x hx y => ?_⟩
      rw [hc_eq x hx y]
      have hev : (a.map (Polynomial.evalRingHom x)).eval y =
          MvPolynomial.eval (fun i => if i = 0 then x else y) (g (μ k.succ) - g (μ k.castSucc)) := by
        simpa [a] using eval_toPolyY (g (μ k.succ) - g (μ k.castSucc)) (fun i => if i = 0 then x else y)
      rw [hev]
  choose c hc_SI hc_eq using hstep
  let d : (Fin 2 → ℝ) → ℝ := fun z =>
    MvPolynomial.eval z (g (μ 0)) + ∑ k : Fin s, c k z
  have hd_SI : SI d := SI_add (SI_poly _) (SI_finset_sum Finset.univ c fun k _ => hc_SI k)
  refine ⟨d, hd_SI, fun x hx y => ?_⟩
  -- Telescoping sum equals f on every open cell, hence everywhere on {x} × ℝ by continuity!
  have hd_cell : ∀ (m : Fin (s + 1)) (y' : ℝ),
      (fun i => if i = 0 then x else y') ∈ vertCell U ξ m →
      d (fun i => if i = 0 then x else y') = f (fun i => if i = 0 then x else y') := by
    intro m y' hy'
    rw [hμ m _ hy']
    dsimp only [d]
    have hsum_eq : ∑ k : Fin s, c k (fun i => if i = 0 then x else y') =
        ∑ k : Fin s, if k.val < m.val then
          (MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ k.succ)) -
           MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ k.castSucc))) else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hc_eq k x hx y', map_sub]
      by_cases hkm : k.val < m.val
      · rw [if_pos hkm, if_pos]
        have hpos : 0 < m.val := by omega
        have hle : k ≤ ⟨m.val - 1, by omega⟩ := by show k.val ≤ m.val - 1; omega
        exact ((hmono x hx).monotone hle).trans_lt (hy'.2.1 hpos)
      · rw [if_neg hkm, if_neg]
        have hlt : m.val < s := by omega
        have hle : ⟨m.val, hlt⟩ ≤ k := by show m.val ≤ k.val; omega
        exact not_lt.mpr ((hy'.2.2 hlt).le.trans ((hmono x hx).monotone hle))
    rw [hsum_eq]
    -- Telescoping sum over k : Fin s with k.val < m.val
    let F : ℕ → ℝ := fun n =>
      if h : n < s + 1 then MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ ⟨n, h⟩)) else 0
    have htele : ∀ n : ℕ, n ≤ s →
        F 0 + ∑ k : Fin s, (if k.val < n then F (k.val + 1) - F k.val else 0) = F n := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hsplit : ∑ k : Fin s, (if k.val < n + 1 then F (k.val + 1) - F k.val else 0) =
            (∑ k : Fin s, (if k.val < n then F (k.val + 1) - F k.val else 0)) +
            (F (n + 1) - F n) := by
          let k0 : Fin s := ⟨n, by omega⟩
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k0),
              ← Finset.add_sum_erase (Finset.univ) (fun k : Fin s => if k.val < n then F (k.val + 1) - F k.val else 0) (Finset.mem_univ k0)]
          simp only [k0, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, lt_self_iff_false, zero_add]
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          have hne : k.val ≠ n := fun h => (Finset.mem_erase.mp hk).1 (Fin.ext h)
          have hiff : k.val < n + 1 ↔ k.val < n := by omega
          simp only [hiff]
        rw [hsplit, ← add_assoc, ih (by omega)]
        ring
    have hfin := htele m.val (by omega)
    have hF0 : F 0 = MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ 0)) := by simp [F]
    have hFm : F m.val = MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ m)) :=
      dif_pos m.isLt
    have hFsum : ∑ k : Fin s, (if k.val < m.val then F (k.val + 1) - F k.val else 0) =
        ∑ k : Fin s, if k.val < m.val then
          (MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ k.succ)) -
           MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ k.castSucc))) else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs
      · have h1 : F (k.val + 1) = MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ k.succ)) :=
          dif_pos (Nat.succ_lt_succ k.isLt)
        have h2 : F k.val = MvPolynomial.eval (fun i => if i = 0 then x else y') (g (μ k.castSucc)) :=
          dif_pos (Nat.lt_succ_of_lt k.isLt)
        rw [h1, h2]
      · rfl
    rw [← hFsum, ← hF0, hfin, hFm]
  -- Now prove d (x, y) = f (x, y) by continuity, approaching y from outside the finite set {ξ k x}.
  by_contra hne
  let δ := |d (fun i => if i = 0 then x else y) - f (fun i => if i = 0 then x else y)| / 2
  have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hne))
  have hcont_df : Continuous (fun y' => d (fun i => if i = 0 then x else y') -
      f (fun i => if i = 0 then x else y')) :=
    ((SI_continuous hd_SI).comp (continuous_pi fun i => by fin_cases i <;> [exact continuous_const; exact continuous_id])).sub
      (hf.comp (continuous_pi fun i => by fin_cases i <;> [exact continuous_const; exact continuous_id]))
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp hcont_df.continuousAt δ hδ
  have hinf : (Set.Ioo (y - ε) (y + ε) \ ↑(Finset.univ.image (fun k : Fin s => ξ k x))).Nonempty :=
    ((Set.Ioo_infinite (by linarith : y - ε < y + ε)).diff (Finset.finite_toSet _)).nonempty
  obtain ⟨y', hy'_Ioo, hy'_not⟩ := hinf
  have hy'_nξ : ∀ k : Fin s, y' ≠ ξ k x := fun k heq =>
    hy'_not (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, heq.symm⟩))
  -- Find cell m containing (x, y')
  let S_lt : Finset (Fin s) := Finset.univ.filter fun k => ξ k x < y'
  have hcell_ex : ∃ m : Fin (s + 1), (fun i => if i = 0 then x else y') ∈ vertCell U ξ m := by
    by_cases hsne : S_lt.Nonempty
    · let k0 := S_lt.max' hsne
      have hk0_lt : ξ k0 x < y' := (Finset.mem_filter.mp (Finset.max'_mem S_lt hsne)).2
      refine ⟨⟨k0.val + 1, by omega⟩, hx, fun _ => ?_, fun h => ?_⟩
      · have heq : (⟨k0.val + 1 - 1, by omega⟩ : Fin s) = k0 := by ext; simp
        simpa [heq] using hk0_lt
      · by_contra hle
        have hlt' : ξ ⟨k0.val + 1, h⟩ x < y' := lt_of_le_of_ne (not_lt.mp hle) (hy'_nξ _).symm
        have hin : ⟨k0.val + 1, h⟩ ∈ S_lt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩
        have hle' : (⟨k0.val + 1, h⟩ : Fin s) ≤ k0 := Finset.le_max' S_lt ⟨k0.val + 1, h⟩ hin
        have hle'' : k0.val + 1 ≤ k0.val := hle'
        omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hsne
      refine ⟨⟨0, by omega⟩, hx, fun h => False.elim (Nat.not_lt_zero _ h), fun h => ?_⟩
      by_contra hle
      have hlt' : ξ ⟨0, h⟩ x < y' := lt_of_le_of_ne (not_lt.mp hle) (hy'_nξ _).symm
      have : ⟨0, h⟩ ∈ S_lt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩
      rw [hsne] at this; exact False.elim (Finset.notMem_empty _ this)
  obtain ⟨m, hm⟩ := hcell_ex
  have hdist : dist y' y < ε := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy'_Ioo.1, hy'_Ioo.2]
  have hlt := hball hdist
  rw [Real.dist_eq, hd_cell m y' hm, sub_self, zero_sub, abs_neg] at hlt
  change |d (fun i => if i = 0 then x else y) - f (fun i => if i = 0 then x else y)| <
    |d (fun i => if i = 0 then x else y) - f (fun i => if i = 0 then x else y)| / 2 at hlt
  linarith [abs_nonneg (d (fun i => if i = 0 then x else y) - f (fun i => if i = 0 then x else y))]

/-- Elementary polynomial bound in a quadrant `σx * (x - x₀) > 0, σy * (y - y₀) > 0`:
    1. If `g(x₀, y₀) = 0`, then `g(x, y) ≤ C * max L (L ^ e)` for odd `e = 2 * deg + 1`.
    2. For any `δ > 0`, on `L ≥ δ`, `g(x, y) ≤ C' * L ^ e`. -/
lemma quadrant_poly_bound (g : MvPolynomial (Fin 2) ℝ) (x₀ y₀ σx σy : ℝ)
    (hσx : σx * σx = 1) (hσy : σy * σy = 1) :
    let e : ℕ := 2 * g.totalDegree + 1
    let L : MvPolynomial (Fin 2) ℝ :=
      MvPolynomial.C σx * (MvPolynomial.X 0 - MvPolynomial.C x₀) +
      MvPolynomial.C σy * (MvPolynomial.X 1 - MvPolynomial.C y₀)
    (MvPolynomial.eval (fun i => if i = 0 then x₀ else y₀) g = 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ,
        0 ≤ σx * (z 0 - x₀) → 0 ≤ σy * (z 1 - y₀) →
        MvPolynomial.eval z g ≤ C * max (MvPolynomial.eval z L) ((MvPolynomial.eval z L) ^ e)) ∧
    (∀ δ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ,
      0 ≤ σx * (z 0 - x₀) → 0 ≤ σy * (z 1 - y₀) → δ ≤ MvPolynomial.eval z L →
      MvPolynomial.eval z g ≤ C * (MvPolynomial.eval z L) ^ e) := by
  classical
  set e : ℕ := 2 * g.totalDegree + 1
  set L : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.C σx * (MvPolynomial.X 0 - MvPolynomial.C x₀) +
    MvPolynomial.C σy * (MvPolynomial.X 1 - MvPolynomial.C y₀)
  -- Express g in shifted coordinates u = σx * (x - x₀), v = σy * (y - y₀)
  let h : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.aeval (fun i : Fin 2 =>
      if i = 0 then MvPolynomial.C x₀ + MvPolynomial.C σx * MvPolynomial.X 0
      else MvPolynomial.C y₀ + MvPolynomial.C σy * MvPolynomial.X 1) g
  have hh_eval : ∀ z : Fin 2 → ℝ,
      MvPolynomial.eval (fun i => if i = 0 then σx * (z 0 - x₀) else σy * (z 1 - y₀)) h =
        MvPolynomial.eval z g := by
    intro z
    dsimp only [h]
    induction g using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      congr 1
      fin_cases i
      · simp only [Fin.zero_eta, MvPolynomial.aeval_X, ↓reduceIte, map_add, map_mul,
          MvPolynomial.eval_C, MvPolynomial.eval_X]
        have : x₀ + σx * (σx * (z 0 - x₀)) = x₀ + (σx * σx) * (z 0 - x₀) := by ring
        rw [this, hσx]; ring
      · simp only [Fin.mk_one, MvPolynomial.aeval_X, Fin.isValue, one_ne_zero,
          ↓reduceIte, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
        have : y₀ + σy * (σy * (z 1 - y₀)) = y₀ + (σy * σy) * (z 1 - y₀) := by ring
        rw [this, hσy]; ring
  have hh_deg : h.totalDegree ≤ g.totalDegree := by
    let φ : Fin 2 → MvPolynomial (Fin 2) ℝ := fun i =>
      if i = 0 then MvPolynomial.C x₀ + MvPolynomial.C σx * MvPolynomial.X 0
      else MvPolynomial.C y₀ + MvPolynomial.C σy * MvPolynomial.X 1
    have hφ_deg : ∀ i : Fin 2, (φ i).totalDegree ≤ 1 := by
      intro i; fin_cases i
      · apply (MvPolynomial.totalDegree_add _ _).trans
        rw [MvPolynomial.totalDegree_C]
        exact max_le (Nat.zero_le 1) ((MvPolynomial.totalDegree_mul _ _).trans (by simp))
      · apply (MvPolynomial.totalDegree_add _ _).trans
        rw [MvPolynomial.totalDegree_C]
        exact max_le (Nat.zero_le 1) ((MvPolynomial.totalDegree_mul _ _).trans (by simp))
    have hsum : h = ∑ m ∈ g.support, MvPolynomial.C (g.coeff m) *
        (φ 0 ^ m 0 * φ 1 ^ m 1) := by
      conv_lhs => rw [show h = MvPolynomial.aeval φ g from rfl, g.as_sum, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.aeval_monomial]
      change MvPolynomial.C (g.coeff m) * (m.prod fun i k => φ i ^ k) =
        MvPolynomial.C (g.coeff m) * (φ 0 ^ m 0 * φ 1 ^ m 1)
      congr 1
      rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ m.support) _ (fun _ _ => pow_zero _)]
      rw [Fin.prod_univ_two]
    rw [hsum]
    apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    rw [Finset.sup_le_iff]
    intro m hm
    have hm_deg : m 0 + m 1 ≤ g.totalDegree := by
      have h1 : (m.sum fun _ e => e) ≤ g.totalDegree :=
        Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ e => e) hm
      have h2 : (m.sum fun _ e => e) = m 0 + m 1 := by
        rw [Finsupp.sum,
          Finset.sum_subset (Finset.subset_univ m.support) (fun i _ hi => Finsupp.notMem_support_iff.mp hi),
          Fin.sum_univ_two]
      omega
    calc (MvPolynomial.C (g.coeff m) * (φ 0 ^ m 0 * φ 1 ^ m 1)).totalDegree
        ≤ (MvPolynomial.C (g.coeff m)).totalDegree + (φ 0 ^ m 0 * φ 1 ^ m 1).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + ((φ 0 ^ m 0).totalDegree + (φ 1 ^ m 1).totalDegree) := by
          rw [MvPolynomial.totalDegree_C]; exact Nat.add_le_add_left (MvPolynomial.totalDegree_mul _ _) 0
      _ ≤ m 0 * (φ 0).totalDegree + m 1 * (φ 1).totalDegree := by
          rw [zero_add]
          exact Nat.add_le_add (MvPolynomial.totalDegree_pow _ _) (MvPolynomial.totalDegree_pow _ _)
      _ ≤ m 0 * 1 + m 1 * 1 :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (hφ_deg 0)) (Nat.mul_le_mul_left _ (hφ_deg 1))
      _ ≤ g.totalDegree := by omega
  set C0 : ℝ := ∑ m ∈ h.support, |h.coeff m|
  have hC0_nn : 0 ≤ C0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmon_bd : ∀ (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (m : Fin 2 →₀ ℕ),
      (∏ i : Fin 2, (if i = 0 then u else v) ^ m i) ≤ (u + v) ^ m.degree := by
    intro u v hu hv m
    have hprod : (∏ i : Fin 2, (if i = 0 then u else v) ^ m i) = u ^ (m 0) * v ^ (m 1) := by
      rw [Fin.prod_univ_two]; simp
    have hdeg : m.degree = m 0 + m 1 := by
      rw [Finsupp.degree_apply]
      rw [Finset.sum_subset (Finset.subset_univ m.support) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)]
      rw [Fin.sum_univ_two]
    rw [hprod, hdeg, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hu (by linarith) _) (pow_le_pow_left₀ hv (by linarith) _)
      (pow_nonneg hv _) (pow_nonneg (by linarith) _)
  constructor
  · intro hg0
    refine ⟨C0, hC0_nn, fun z hu hv => ?_⟩
    set u := σx * (z 0 - x₀)
    set v := σy * (z 1 - y₀)
    have hL_eq : MvPolynomial.eval z L = u + v := by simp [L, u, v]
    rw [hL_eq, ← hh_eval z, MvPolynomial.eval_eq']
    have hcoeff0 : h.coeff 0 = 0 := by
      have h0 := hh_eval (fun i => if i = 0 then x₀ else y₀)
      have hzero : (fun i : Fin 2 =>
          if i = 0 then σx * ((if (0 : Fin 2) = 0 then x₀ else y₀) - x₀)
          else σy * ((if (1 : Fin 2) = 0 then x₀ else y₀) - y₀)) = 0 := by
        ext i; fin_cases i <;> simp
      rw [hzero, hg0, MvPolynomial.eval_zero] at h0
      exact h0
    calc ∑ m ∈ h.support, h.coeff m * ∏ i : Fin 2, (if i = 0 then u else v) ^ m i
        ≤ ∑ m ∈ h.support, |h.coeff m| * max (u + v) ((u + v) ^ e) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm_ne : m ≠ 0 := fun h0 => by
            subst h0; exact (MvPolynomial.mem_support_iff.mp hm) hcoeff0
          have hm_deg_pos : 1 ≤ m.degree := by
            by_contra hlt
            have h0 : m.degree = 0 := by omega
            apply hm_ne
            ext i
            have : m i ≤ m.degree := by
              rw [Finsupp.degree_apply]
              by_cases hi : i ∈ m.support
              · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
              · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _
            change m i = 0; omega
          have hm_deg_le : m.degree ≤ e := by
            have h1 : m.degree ≤ h.totalDegree := by
              rw [Finsupp.degree_apply]
              exact Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ e => e) hm
            omega
          have hpow_le : (u + v) ^ m.degree ≤ max (u + v) ((u + v) ^ e) := by
            by_cases h1 : u + v ≤ 1
            · exact (pow_le_pow_of_le_one (by linarith) h1 hm_deg_pos).trans (by
                rw [pow_one]; exact le_max_left _ _)
            · exact (pow_le_pow_right₀ (by linarith) hm_deg_le).trans (le_max_right _ _)
          have hprod_nn : 0 ≤ ∏ i : Fin 2, (if i = 0 then u else v) ^ m i :=
            Finset.prod_nonneg fun i _ => pow_nonneg (by split_ifs <;> assumption) _
          calc h.coeff m * ∏ i : Fin 2, (if i = 0 then u else v) ^ m i
              ≤ |h.coeff m| * ∏ i : Fin 2, (if i = 0 then u else v) ^ m i :=
                mul_le_mul_of_nonneg_right (le_abs_self _) hprod_nn
            _ ≤ |h.coeff m| * (u + v) ^ m.degree :=
                mul_le_mul_of_nonneg_left (hmon_bd u v hu hv m) (abs_nonneg _)
            _ ≤ |h.coeff m| * max (u + v) ((u + v) ^ e) :=
                mul_le_mul_of_nonneg_left hpow_le (abs_nonneg _)
      _ = C0 * max (u + v) ((u + v) ^ e) := (Finset.sum_mul _ _ _).symm
  · intro δ hδ
    refine ⟨C0 * (1 / δ ^ e + 1), by positivity, fun z hu hv hLδ => ?_⟩
    set u := σx * (z 0 - x₀)
    set v := σy * (z 1 - y₀)
    have hL_eq : MvPolynomial.eval z L = u + v := by simp [L, u, v]
    rw [hL_eq] at hLδ ⊢
    rw [← hh_eval z, MvPolynomial.eval_eq']
    calc ∑ m ∈ h.support, h.coeff m * ∏ i : Fin 2, (if i = 0 then u else v) ^ m i
        ≤ ∑ m ∈ h.support, |h.coeff m| * ((1 / δ ^ e + 1) * (u + v) ^ e) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm_deg_le : m.degree ≤ e := by
            have h1 : m.degree ≤ h.totalDegree := by
              rw [Finsupp.degree_apply]
              exact Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ e => e) hm
            omega
          have hpow_le : (u + v) ^ m.degree ≤ (1 / δ ^ e + 1) * (u + v) ^ e := by
            by_cases h1 : u + v ≤ 1
            · have hle1 : (u + v) ^ m.degree ≤ 1 := pow_le_one₀ (by linarith) h1
              have hδe : δ ^ e ≤ (u + v) ^ e := pow_le_pow_left₀ hδ.le hLδ e
              have h1le : 1 ≤ (1 / δ ^ e) * (u + v) ^ e := by
                rw [one_div, inv_mul_eq_div, one_le_div (pow_pos hδ e)]
                exact hδe
              have hnn : 0 ≤ (u + v) ^ e := pow_nonneg (by linarith) e
              nlinarith
            · have hle2 : (u + v) ^ m.degree ≤ (u + v) ^ e := pow_le_pow_right₀ (by linarith) hm_deg_le
              have hnn : 0 ≤ (1 / δ ^ e) * (u + v) ^ e := by positivity
              nlinarith
          have hprod_nn : 0 ≤ ∏ i : Fin 2, (if i = 0 then u else v) ^ m i :=
            Finset.prod_nonneg fun i _ => pow_nonneg (by split_ifs <;> assumption) _
          calc h.coeff m * ∏ i : Fin 2, (if i = 0 then u else v) ^ m i
              ≤ |h.coeff m| * ∏ i : Fin 2, (if i = 0 then u else v) ^ m i :=
                mul_le_mul_of_nonneg_right (le_abs_self _) hprod_nn
            _ ≤ |h.coeff m| * (u + v) ^ m.degree :=
                mul_le_mul_of_nonneg_left (hmon_bd u v hu hv m) (abs_nonneg _)
            _ ≤ |h.coeff m| * ((1 / δ ^ e + 1) * (u + v) ^ e) :=
                mul_le_mul_of_nonneg_left hpow_le (abs_nonneg _)
      _ = C0 * (1 / δ ^ e + 1) * (u + v) ^ e := by rw [← Finset.sum_mul]; ring

lemma odd_pow_nonpos {a : ℝ} (ha : a ≤ 0) (n : ℕ) : a ^ (2 * n + 1) ≤ 0 := by
  rw [pow_succ, pow_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (sq_nonneg a) n) ha

theorem pierce_birkhoff_dim_two_SI (f : (Fin 2 → ℝ) → ℝ) (hf : PierceBirkhoff.IsPiecewiseMvPolynomial f) :
    SI f := by
  classical
  obtain ⟨ι, P, g, hfin, hcl, _, hcov, heq⟩ := hf
  haveI : Fintype ι := Fintype.ofFinite ι
  have hf_cont : Continuous f := continuous_of_piecewise hcl hcov heq
  have hval : ∀ x, ∃ i, f x = MvPolynomial.eval x (g i) := by
    intro x
    have hx : x ∈ ⋃ i, P i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, heq i x hi⟩
  -- Step 1: Vertical strips (in y over x)
  let diffY : Finset (Polynomial (Polynomial ℝ)) :=
    (Finset.univ ×ˢ Finset.univ).image fun p : ι × ι => toPolyY (g p.1 - g p.2)
  obtain ⟨By, hBy_nz, hBy_mem, hBy_neg, hBy_der, hBy_rem⟩ := exists_polyY_closure diffY
  obtain ⟨CritX, hProjX⟩ := projection_poly By hBy_nz
  have hB_diffY : ∀ i j, g i ≠ g j → toPolyY (g i - g j) ∈ By := by
    intro i j hij
    apply hBy_mem _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    intro h0
    have := congrArg fromPolyY h0
    rw [fromPolyY_toPolyY, map_zero, sub_eq_zero] at this
    exact hij this
  have hd_vert : ∀ p : Fin (CritX.card + 1), ∃ d : (Fin 2 → ℝ) → ℝ, SI d ∧
      ∀ x ∈ critInterval CritX p, ∀ y : ℝ,
        d (fun i => if i = 0 then x else y) = f (fun i => if i = 0 then x else y) := by
    intro p
    obtain ⟨s, ξ, hmono, hcont, hroots, hdich⟩ :=
      hProjX (critInterval CritX p) (critInterval_open CritX p) (critInterval_connected CritX p)
        (critInterval_disj CritX p)
    exact vertical_strip_SI hf_cont hval By hB_diffY hBy_neg hBy_der hBy_rem
      (critInterval_open CritX p) (critInterval_connected CritX p) hmono hcont hroots hdich
  choose dVert hdVert_SI hdVert_eq using hd_vert
  -- Step 2: Horizontal strips (swap coordinates: x over y), also including {x - γ | γ ∈ CritX}!
  let sw : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun z i => z (1 - i)
  have hsw_invol : ∀ z, sw (sw z) = z := fun z => by ext i; fin_cases i <;> rfl
  have hsw_cont : Continuous sw := continuous_pi fun i => by fin_cases i <;> exact continuous_apply _
  let fSw : (Fin 2 → ℝ) → ℝ := fun z => f (sw z)
  let gSw : ι → MvPolynomial (Fin 2) ℝ := fun i => MvPolynomial.rename (fun k : Fin 2 => 1 - k) (g i)
  have hfSw_cont : Continuous fSw := hf_cont.comp hsw_cont
  have hvalSw : ∀ z, ∃ i, fSw z = MvPolynomial.eval z (gSw i) := by
    intro z
    obtain ⟨i, hi⟩ := hval (sw z)
    refine ⟨i, ?_⟩
    simp only [fSw, gSw, MvPolynomial.eval_rename, Function.comp_def]
    exact hi
  let diffX : Finset (Polynomial (Polynomial ℝ)) :=
    ((Finset.univ ×ˢ Finset.univ).image fun p : ι × ι => toPolyY (gSw p.1 - gSw p.2)) ∪
    (CritX.image fun γ => toPolyY (MvPolynomial.X 1 - MvPolynomial.C γ))
  obtain ⟨Bx, hBx_nz, hBx_mem, hBx_neg, hBx_der, hBx_rem⟩ := exists_polyY_closure diffX
  obtain ⟨CritY, hProjY⟩ := projection_poly Bx hBx_nz
  have hB_diffX : ∀ i j, gSw i ≠ gSw j → toPolyY (gSw i - gSw j) ∈ Bx := by
    intro i j hij
    apply hBx_mem _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    intro h0
    have := congrArg fromPolyY h0
    rw [fromPolyY_toPolyY, map_zero, sub_eq_zero] at this
    exact hij this
  have hB_critX : ∀ γ ∈ CritX, toPolyY (MvPolynomial.X 1 - MvPolynomial.C γ) ∈ Bx := by
    intro γ hγ
    apply hBx_mem _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩))
    intro h0
    have := congrArg (fun p => MvPolynomial.eval (fun _ => γ + 1) (fromPolyY p)) h0
    rw [fromPolyY_toPolyY, map_zero, map_zero, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at this
    linarith
  have hd_horiz : ∀ q : Fin (CritY.card + 1),
      ∃ (e : (Fin 2 → ℝ) → ℝ) (s : ℕ) (ζ : Fin s → ℝ → ℝ),
        SI e ∧
        (∀ y ∈ critInterval CritY q, ∀ x : ℝ,
          e (fun i => if i = 0 then x else y) = f (fun i => if i = 0 then x else y)) ∧
        (∀ y ∈ critInterval CritY q, StrictMono (fun k => ζ k y)) ∧
        (∀ k : Fin s, ContinuousOn (ζ k) (critInterval CritY q)) ∧
        (∀ a ∈ Bx, ∀ y ∈ critInterval CritY q, ∀ x : ℝ,
          (a.map (Polynomial.evalRingHom y)).eval x = 0 → ∃ k : Fin s, x = ζ k y) := by
    intro q
    obtain ⟨s, ζ, hmono, hcont, hroots, hdich⟩ :=
      hProjY (critInterval CritY q) (critInterval_open CritY q) (critInterval_connected CritY q)
        (critInterval_disj CritY q)
    obtain ⟨eSw, heSw_SI, heSw_eq⟩ :=
      vertical_strip_SI hfSw_cont hvalSw Bx hB_diffX hBx_neg hBx_der hBx_rem
        (critInterval_open CritY q) (critInterval_connected CritY q) hmono hcont hroots hdich
    refine ⟨fun z => eSw (sw z), s, ζ, SI_swap heSw_SI, ?_, hmono, hcont, hroots⟩
    · intro y hy x
      have hsw_eq : sw (fun i => if i = 0 then x else y) = (fun i => if i = 0 then y else x) := by
        ext i; fin_cases i <;> rfl
      dsimp only
      rw [hsw_eq, heSw_eq y hy x]
      simp only [fSw, ← hsw_eq, hsw_invol]
  -- Wait: refine had 1 extra goal? Let's unpack cleanly!
  have hd_horiz' : ∀ q : Fin (CritY.card + 1),
      ∃ (e : (Fin 2 → ℝ) → ℝ), SI e ∧
        (∀ y ∈ critInterval CritY q, ∀ x : ℝ,
          e (fun i => if i = 0 then x else y) = f (fun i => if i = 0 then x else y)) ∧
        ∃ (s : ℕ) (ζ : Fin s → ℝ → ℝ),
          (∀ y ∈ critInterval CritY q, StrictMono (fun k => ζ k y)) ∧
          (∀ k : Fin s, ContinuousOn (ζ k) (critInterval CritY q)) ∧
          (∀ a ∈ Bx, ∀ y ∈ critInterval CritY q, ∀ x : ℝ,
            (a.map (Polynomial.evalRingHom y)).eval x = 0 → ∃ k : Fin s, x = ζ k y) := by
    intro q
    obtain ⟨e, s, ζ, hSI, heq', hmono, hcont, hroots⟩ := hd_horiz q
    exact ⟨e, hSI, heq', s, ζ, hmono, hcont, hroots⟩
  choose eHoriz heHoriz_SI heHoriz_eq sH ζH hζ_mono hζ_cont hζ_roots using hd_horiz'
  -- Step 3: Index all open cells E_{q, k} = sw '' vertCell (critInterval CritY q) (ζH q) k
  let CellIdx := Σ q : Fin (CritY.card + 1), Fin (sH q + 1)
  haveI : Fintype CellIdx := inferInstance
  haveI : Nonempty CellIdx := ⟨⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
  let E : CellIdx → Set (Fin 2 → ℝ) := fun idx =>
    sw ⁻¹' vertCell (critInterval CritY idx.1) (ζH idx.1) idx.2
  have hE_conn : ∀ idx : CellIdx, IsConnected (E idx) := by
    intro idx
    have heq_img : E idx = sw '' vertCell (critInterval CritY idx.1) (ζH idx.1) idx.2 := by
      ext z
      simp only [E, Set.mem_preimage, Set.mem_image]
      constructor
      · intro hz; exact ⟨sw z, hz, hsw_invol z⟩
      · rintro ⟨w, hw, rfl⟩; rwa [hsw_invol]
    rw [heq_img]
    exact (vertCell_connected (critInterval_connected CritY idx.1) (hζ_mono idx.1) (hζ_cont idx.1) idx.2).image
      sw hsw_cont.continuousOn
  -- Each E idx lies in a unique vertical strip critInterval CritX (px idx) and has a unique piece g (ν idx).
  have hE_strip_piece : ∀ idx : CellIdx,
      ∃ (px : Fin (CritX.card + 1)) (ν : ι),
        (∀ z ∈ E idx, z 0 ∈ critInterval CritX px ∧ z 1 ∈ critInterval CritY idx.1) ∧
        (∀ z ∈ E idx, f z = MvPolynomial.eval z (g ν)) := by
    intro idx
    have hE_no_critX : ∀ z ∈ E idx, z 0 ∉ CritX := by
      intro z hz hγ
      have h0 : ((toPolyY (MvPolynomial.X 1 - MvPolynomial.C (z 0))).map
          (Polynomial.evalRingHom (z 1))).eval (z 0) = 0 := by
        have := eval_toPolyY (MvPolynomial.X 1 - MvPolynomial.C (z 0)) (sw z)
        simpa [sw] using this
      obtain ⟨m, hm⟩ := hζ_roots idx.1 _ (hB_critX (z 0) hγ) (z 1) hz.1 (z 0) h0
      by_cases hmk : m.val < idx.2.val
      · have hpos : 0 < idx.2.val := by omega
        have hle : m ≤ ⟨idx.2.val - 1, by omega⟩ := by show m.val ≤ idx.2.val - 1; omega
        have hlt1 : ζH idx.1 ⟨idx.2.val - 1, by omega⟩ (z 1) < z 0 := hz.2.1 hpos
        linarith [hlt1, (hζ_mono idx.1 (z 1) hz.1).monotone hle, hm]
      · have hlt : idx.2.val < sH idx.1 := by omega
        have hle : ⟨idx.2.val, hlt⟩ ≤ m := by show idx.2.val ≤ m.val; omega
        have hlt2 : z 0 < ζH idx.1 ⟨idx.2.val, hlt⟩ (z 1) := hz.2.2 hlt
        linarith [hlt2, (hζ_mono idx.1 (z 1) hz.1).monotone hle, hm]
    obtain ⟨z0, hz0⟩ := (hE_conn idx).nonempty
    obtain ⟨px, hpx0⟩ := critInterval_cover CritX (z0 0) (hE_no_critX z0 hz0)
    have hE_in_px : ∀ z ∈ E idx, z 0 ∈ critInterval CritX px := by
      let A : Set (Fin 2 → ℝ) := {z | z 0 ∈ critInterval CritX px}
      let A' : Set (Fin 2 → ℝ) := ⋃ p' : {p' : Fin (CritX.card + 1) // p' ≠ px},
        {z | z 0 ∈ critInterval CritX p'.1}
      have hA_open : IsOpen A := (critInterval_open CritX px).preimage (continuous_apply 0)
      have hA'_open : IsOpen A' := isOpen_iUnion fun p' =>
        (critInterval_open CritX p'.1).preimage (continuous_apply 0)
      have hdisj : ∀ z, z ∈ A → z ∈ A' → False := by
        intro z hzA hzA'
        obtain ⟨⟨p', hp'⟩, hzp'⟩ := Set.mem_iUnion.mp hzA'
        rcases lt_or_gt_of_ne hp' with hlt | hgt
        · obtain ⟨γ, _, h1, h2⟩ := critInterval_sep CritX hlt
          linarith [h1 (z 0) hzp', h2 (z 0) hzA]
        · obtain ⟨γ, _, h1, h2⟩ := critInterval_sep CritX hgt
          linarith [h1 (z 0) hzA, h2 (z 0) hzp']
      have hcovE : E idx ⊆ A ∪ A' := by
        intro z hz
        obtain ⟨p', hp'⟩ := critInterval_cover CritX (z 0) (hE_no_critX z hz)
        by_cases heqp : p' = px
        · subst heqp; exact Or.inl hp'
        · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨p', heqp⟩, hp'⟩)
      intro z hz
      by_contra hnot
      have hzA' : z ∈ A' := (hcovE hz).resolve_left hnot
      obtain ⟨w, _, hwA, hwA'⟩ := (hE_conn idx).isPreconnected A A' hA_open hA'_open hcovE
        ⟨z0, hz0, hpx0⟩ ⟨z, hz, hzA'⟩
      exact hdisj w hwA hwA'
    -- Find unique piece ν on E idx
    have hE_piece : ∃ ν : ι, ∀ z ∈ E idx, f z = MvPolynomial.eval z (g ν) := by
      apply const_piece_on_connected hf_cont hval (hE_conn idx)
      intro i j hij z hz heq'
      have hijSw : gSw i ≠ gSw j := by
        intro hSw
        apply hij
        have h1 := congrArg (MvPolynomial.rename (fun k : Fin 2 => 1 - k)) hSw
        have hcomp : ∀ p : MvPolynomial (Fin 2) ℝ,
            MvPolynomial.rename (fun k : Fin 2 => 1 - k)
              (MvPolynomial.rename (fun k : Fin 2 => 1 - k) p) = p := by
          intro p
          rw [MvPolynomial.rename_rename]
          have : ((fun k : Fin 2 => 1 - k) ∘ (fun k : Fin 2 => 1 - k)) = id := by
            funext k; fin_cases k <;> rfl
          rw [this, MvPolynomial.rename_id]
          rfl
        simpa [gSw, hcomp] using h1
      have h0 : ((toPolyY (gSw i - gSw j)).map (Polynomial.evalRingHom (z 1))).eval (z 0) = 0 := by
        have h1 := eval_toPolyY (gSw i - gSw j) (sw z)
        have h2 : MvPolynomial.eval (sw z) (gSw i - gSw j) =
            MvPolynomial.eval z (g i) - MvPolynomial.eval z (g j) := by
          simp only [map_sub, gSw, MvPolynomial.eval_rename, Function.comp_def]
          have : (fun k : Fin 2 => sw z (1 - k)) = z := by ext k; fin_cases k <;> rfl
          rw [this]
        rw [h2, heq', sub_self] at h1
        simpa [sw] using h1
      obtain ⟨m, hm⟩ := hζ_roots idx.1 _ (hB_diffX i j hijSw) (z 1) hz.1 (z 0) h0
      by_cases hmk : m.val < idx.2.val
      · have hpos : 0 < idx.2.val := by omega
        have hle : m ≤ ⟨idx.2.val - 1, by omega⟩ := by show m.val ≤ idx.2.val - 1; omega
        have hlt1 : ζH idx.1 ⟨idx.2.val - 1, by omega⟩ (z 1) < z 0 := hz.2.1 hpos
        linarith [hlt1, (hζ_mono idx.1 (z 1) hz.1).monotone hle, hm]
      · have hlt : idx.2.val < sH idx.1 := by omega
        have hle : ⟨idx.2.val, hlt⟩ ≤ m := by show idx.2.val ≤ m.val; omega
        have hlt2 : z 0 < ζH idx.1 ⟨idx.2.val, hlt⟩ (z 1) := hz.2.2 hlt
        linarith [hlt2, (hζ_mono idx.1 (z 1) hz.1).monotone hle, hm]
    obtain ⟨ν, hν⟩ := hE_piece
    exact ⟨px, ν, fun z hz => ⟨hE_in_px z hz, hz.1⟩, hν⟩
  choose px ν hE_in hE_val using hE_strip_piece
  -- Step 4: Pairwise separator u_{a, b} ∈ SI with u_{a, b} ≤ g (ν a) on E a and u_{a, b} ≥ g (ν b) on E b.
  have hpair : ∀ a b : CellIdx, ∃ u : (Fin 2 → ℝ) → ℝ, SI u ∧
      (∀ z ∈ E a, u z ≤ MvPolynomial.eval z (g (ν a))) ∧
      (∀ z ∈ E b, MvPolynomial.eval z (g (ν b)) ≤ u z) := by
    intro a b
    by_cases hp : px a = px b
    · refine ⟨dVert (px a), hdVert_SI (px a), fun z hz => ?_, fun z hz => ?_⟩
      · have hz_eq : (fun i : Fin 2 => if i = 0 then z 0 else z 1) = z := by ext i; fin_cases i <;> rfl
        have h1 := hdVert_eq (px a) (z 0) (hE_in a z hz).1 (z 1)
        rw [hz_eq, hE_val a z hz] at h1; exact h1.le
      · have hz_eq : (fun i : Fin 2 => if i = 0 then z 0 else z 1) = z := by ext i; fin_cases i <;> rfl
        have h1 := hdVert_eq (px a) (z 0) (hp ▸ (hE_in b z hz).1) (z 1)
        rw [hz_eq, hE_val b z hz] at h1; exact h1.ge
    · by_cases hq : a.1 = b.1
      · refine ⟨eHoriz a.1, heHoriz_SI a.1, fun z hz => ?_, fun z hz => ?_⟩
        · have hz_eq : (fun i : Fin 2 => if i = 0 then z 0 else z 1) = z := by ext i; fin_cases i <;> rfl
          have h1 := heHoriz_eq a.1 (z 1) (hE_in a z hz).2 (z 0)
          rw [hz_eq, hE_val a z hz] at h1; exact h1.le
        · have hz_eq : (fun i : Fin 2 => if i = 0 then z 0 else z 1) = z := by ext i; fin_cases i <;> rfl
          have h1 := heHoriz_eq a.1 (z 1) (hq ▸ (hE_in b z hz).2) (z 0)
          rw [hz_eq, hE_val b z hz] at h1; exact h1.ge
      · -- Different vertical and horizontal strips: Mahé's diagonal-strip separator!
        have hx_sep : ∃ (x₀ σx : ℝ), σx * σx = 1 ∧
            (∀ z ∈ E a, σx * (z 0 - x₀) < 0) ∧ (∀ z ∈ E b, 0 < σx * (z 0 - x₀)) := by
          rcases lt_or_gt_of_ne hp with hlt | hgt
          · obtain ⟨γ, _, h1, h2⟩ := critInterval_sep CritX hlt
            exact ⟨γ, 1, by norm_num, fun z hz => by linarith [h1 (z 0) (hE_in a z hz).1],
              fun z hz => by linarith [h2 (z 0) (hE_in b z hz).1]⟩
          · obtain ⟨γ, _, h1, h2⟩ := critInterval_sep CritX hgt
            exact ⟨γ, -1, by norm_num, fun z hz => by linarith [h2 (z 0) (hE_in a z hz).1],
              fun z hz => by linarith [h1 (z 0) (hE_in b z hz).1]⟩
        have hy_sep : ∃ (y₀ σy : ℝ), σy * σy = 1 ∧
            (∀ z ∈ E a, σy * (z 1 - y₀) < 0) ∧ (∀ z ∈ E b, 0 < σy * (z 1 - y₀)) := by
          rcases lt_or_gt_of_ne hq with hlt | hgt
          · obtain ⟨η, _, h1, h2⟩ := critInterval_sep CritY hlt
            exact ⟨η, 1, by norm_num, fun z hz => by linarith [h1 (z 1) (hE_in a z hz).2],
              fun z hz => by linarith [h2 (z 1) (hE_in b z hz).2]⟩
          · obtain ⟨η, _, h1, h2⟩ := critInterval_sep CritY hgt
            exact ⟨η, -1, by norm_num, fun z hz => by linarith [h2 (z 1) (hE_in a z hz).2],
              fun z hz => by linarith [h1 (z 1) (hE_in b z hz).2]⟩
        obtain ⟨x₀, σx, hσx, hax, hbx⟩ := hx_sep
        obtain ⟨y₀, σy, hσy, hay, hby⟩ := hy_sep
        let zc : Fin 2 → ℝ := fun i => if i = 0 then x₀ else y₀
        let diff : MvPolynomial (Fin 2) ℝ := g (ν b) - g (ν a)
        set e : ℕ := 2 * diff.totalDegree + 1
        set L : MvPolynomial (Fin 2) ℝ :=
          MvPolynomial.C σx * (MvPolynomial.X 0 - MvPolynomial.C x₀) +
          MvPolynomial.C σy * (MvPolynomial.X 1 - MvPolynomial.C y₀)
        have hbd := quadrant_poly_bound diff x₀ y₀ σx σy hσx hσy
        by_cases hcl_both : zc ∈ closure (E a) ∧ zc ∈ closure (E b)
        · -- Case 2: corner zc lies in both closures, so diff(zc) = 0!
          have hdiff0 : MvPolynomial.eval zc diff = 0 := by
            have hfa : f zc = MvPolynomial.eval zc (g (ν a)) := by
              have hsub : E a ⊆ {z | f z = MvPolynomial.eval z (g (ν a))} := fun z hz => hE_val a z hz
              exact closure_minimal hsub (isClosed_eq hf_cont (MvPolynomial.continuous_eval _)) hcl_both.1
            have hfb : f zc = MvPolynomial.eval zc (g (ν b)) := by
              have hsub : E b ⊆ {z | f z = MvPolynomial.eval z (g (ν b))} := fun z hz => hE_val b z hz
              exact closure_minimal hsub (isClosed_eq hf_cont (MvPolynomial.continuous_eval _)) hcl_both.2
            simp only [diff, map_sub, ← hfa, ← hfb, sub_self]
          obtain ⟨C, hC_nn, hC⟩ := hbd.1 hdiff0
          let u : (Fin 2 → ℝ) → ℝ := fun z =>
            MvPolynomial.eval z (g (ν a)) +
              C * max 0 (max (MvPolynomial.eval z L) ((MvPolynomial.eval z L) ^ e))
          have hu_SI : SI u := by
            have h1 : SI (fun z => max (MvPolynomial.eval z L) (MvPolynomial.eval z (L ^ e))) :=
              SI_sup (SI_poly L) (SI_poly (L ^ e))
            have h2 : SI (fun z => max 0 (max (MvPolynomial.eval z L) (MvPolynomial.eval z (L ^ e)))) :=
              SI_sup (by simpa using SI_poly 0) h1
            have h3 := SI_add (SI_poly (g (ν a))) (SI_mul_poly (MvPolynomial.C C) h2)
            simpa [u, map_pow] using h3
          refine ⟨u, hu_SI, fun z hz => ?_, fun z hz => ?_⟩
          · have hLneg : MvPolynomial.eval z L ≤ 0 := by
              simp only [L, map_add, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
              linarith [hax z hz, hay z hz]
            have hLe_neg : (MvPolynomial.eval z L) ^ e ≤ 0 := odd_pow_nonpos hLneg diff.totalDegree
            have hmax0 : max 0 (max (MvPolynomial.eval z L) ((MvPolynomial.eval z L) ^ e)) = 0 :=
              max_eq_left (max_le hLneg hLe_neg)
            simp [u, hmax0]
          · have h1 := hC z (hbx z hz).le (hby z hz).le
            simp only [diff, map_sub] at h1
            have h2 : max (MvPolynomial.eval z L) ((MvPolynomial.eval z L) ^ e) ≤
                max 0 (max (MvPolynomial.eval z L) ((MvPolynomial.eval z L) ^ e)) := le_max_right _ _
            have h3 := mul_le_mul_of_nonneg_left h2 hC_nn
            dsimp only [u]; linarith
        · -- Case 1: zc ∉ closure (E a) or zc ∉ closure (E b)
          by_cases hnb : zc ∉ closure (E b)
          · obtain ⟨δ, hδ_pos, hδ⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl zc hnb
            have hLb : ∀ z ∈ E b, δ ≤ MvPolynomial.eval z L := by
              intro z hz
              have hdist : δ ≤ dist z zc := by
                by_contra hlt
                exact hδ (Metric.mem_ball.mpr (not_le.mp hlt)) (subset_closure hz)
              have hL_eq : MvPolynomial.eval z L = |z 0 - x₀| + |z 1 - y₀| := by
                have h1 : σx * (z 0 - x₀) = |z 0 - x₀| := by
                  have hpos := (hbx z hz).le
                  have hsq : |σx| = 1 := by
                    have : |σx| * |σx| = 1 := by rw [← abs_mul, hσx, abs_one]
                    nlinarith [abs_nonneg σx]
                  rw [← abs_of_nonneg hpos, abs_mul, hsq, one_mul]
                have h2 : σy * (z 1 - y₀) = |z 1 - y₀| := by
                  have hpos := (hby z hz).le
                  have hsq : |σy| = 1 := by
                    have : |σy| * |σy| = 1 := by rw [← abs_mul, hσy, abs_one]
                    nlinarith [abs_nonneg σy]
                  rw [← abs_of_nonneg hpos, abs_mul, hsq, one_mul]
                simp only [L, map_add, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, h1, h2]
              rw [hL_eq]
              have hd0 : dist z zc = max |z 0 - x₀| |z 1 - y₀| := by
                have hle : dist z zc ≤ max |z 0 - x₀| |z 1 - y₀| := by
                  rw [dist_pi_le_iff (le_max_of_le_left (abs_nonneg _))]
                  intro i; fin_cases i
                  · simpa [zc, Real.dist_eq] using le_max_left |z 0 - x₀| |z 1 - y₀|
                  · simpa [zc, Real.dist_eq] using le_max_right |z 0 - x₀| |z 1 - y₀|
                have hge : max |z 0 - x₀| |z 1 - y₀| ≤ dist z zc :=
                  max_le (by simpa [zc, Real.dist_eq] using dist_le_pi_dist z zc 0)
                         (by simpa [zc, Real.dist_eq] using dist_le_pi_dist z zc 1)
                exact le_antisymm hle hge
              rw [hd0] at hdist
              have := abs_nonneg (z 0 - x₀)
              have := abs_nonneg (z 1 - y₀)
              rcases max_cases |z 0 - x₀| |z 1 - y₀| with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
            obtain ⟨C, hC_nn, hC⟩ := hbd.2 δ hδ_pos
            let u : (Fin 2 → ℝ) → ℝ := fun z =>
              MvPolynomial.eval z (g (ν a)) + C * max 0 ((MvPolynomial.eval z L) ^ e)
            have hu_SI : SI u := by
              have h1 := SI_add (SI_poly (g (ν a)))
                (SI_mul_poly (MvPolynomial.C C) (SI_sup (by simpa using SI_poly 0) (SI_poly (L ^ e))))
              simpa [u, map_pow] using h1
            refine ⟨u, hu_SI, fun z hz => ?_, fun z hz => ?_⟩
            · have hLneg : MvPolynomial.eval z L ≤ 0 := by
                simp only [L, map_add, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
                linarith [hax z hz, hay z hz]
              have hLe_neg : (MvPolynomial.eval z L) ^ e ≤ 0 := odd_pow_nonpos hLneg diff.totalDegree
              simp [u, max_eq_left hLe_neg]
            · have h1 := hC z (hbx z hz).le (hby z hz).le (hLb z hz)
              simp only [diff, map_sub] at h1
              have h2 := mul_le_mul_of_nonneg_left (le_max_right 0 ((MvPolynomial.eval z L) ^ e)) hC_nn
              dsimp only [u]; linarith
          · have hna : zc ∉ closure (E a) := fun ha => hcl_both ⟨ha, not_not.mp hnb⟩
            obtain ⟨δ, hδ_pos, hδ⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl zc hna
            have hLa : ∀ z ∈ E a, MvPolynomial.eval z L + δ ≤ 0 := by
              intro z hz
              have hdist : δ ≤ dist z zc := by
                by_contra hlt
                exact hδ (Metric.mem_ball.mpr (not_le.mp hlt)) (subset_closure hz)
              have hL_eq : MvPolynomial.eval z L = -(|z 0 - x₀| + |z 1 - y₀|) := by
                have h1 : σx * (z 0 - x₀) = -|z 0 - x₀| := by
                  have hneg := (hax z hz).le
                  have hsq : |σx| = 1 := by
                    have : |σx| * |σx| = 1 := by rw [← abs_mul, hσx, abs_one]
                    nlinarith [abs_nonneg σx]
                  have := abs_of_nonpos hneg
                  rw [abs_mul, hsq, one_mul] at this
                  linarith
                have h2 : σy * (z 1 - y₀) = -|z 1 - y₀| := by
                  have hneg := (hay z hz).le
                  have hsq : |σy| = 1 := by
                    have : |σy| * |σy| = 1 := by rw [← abs_mul, hσy, abs_one]
                    nlinarith [abs_nonneg σy]
                  have := abs_of_nonpos hneg
                  rw [abs_mul, hsq, one_mul] at this
                  linarith
                simp only [L, map_add, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, h1, h2]
                ring
              rw [hL_eq]
              have hle : dist z zc ≤ max |z 0 - x₀| |z 1 - y₀| := by
                rw [dist_pi_le_iff (le_max_of_le_left (abs_nonneg _))]
                intro i; fin_cases i
                · simpa [zc, Real.dist_eq] using le_max_left |z 0 - x₀| |z 1 - y₀|
                · simpa [zc, Real.dist_eq] using le_max_right |z 0 - x₀| |z 1 - y₀|
              have := abs_nonneg (z 0 - x₀)
              have := abs_nonneg (z 1 - y₀)
              rcases max_cases |z 0 - x₀| |z 1 - y₀| with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
            -- On E b, L > 0 so L + δ > δ > 0; shift x₀ to x₀ - σx * δ so L_shift = L + δ!
            have hbd_shift := quadrant_poly_bound diff (x₀ - σx * δ) y₀ σx σy hσx hσy
            obtain ⟨C, hC_nn, hC⟩ := hbd_shift.2 δ hδ_pos
            let L' : MvPolynomial (Fin 2) ℝ := L + MvPolynomial.C δ
            have hL'_eq : ∀ z, MvPolynomial.eval z L' =
                σx * (z 0 - (x₀ - σx * δ)) + σy * (z 1 - y₀) := by
              intro z
              simp only [L', L, map_add, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
              linear_combination -δ * hσx
            let u : (Fin 2 → ℝ) → ℝ := fun z =>
              MvPolynomial.eval z (g (ν a)) + C * max 0 ((MvPolynomial.eval z L') ^ e)
            have hu_SI : SI u := by
              have h1 := SI_add (SI_poly (g (ν a)))
                (SI_mul_poly (MvPolynomial.C C) (SI_sup (by simpa using SI_poly 0) (SI_poly (L' ^ e))))
              simpa [u, map_pow] using h1
            refine ⟨u, hu_SI, fun z hz => ?_, fun z hz => ?_⟩
            · have hL'neg : MvPolynomial.eval z L' ≤ 0 := by
                simpa [L'] using hLa z hz
              have hLe_neg : (MvPolynomial.eval z L') ^ e ≤ 0 := odd_pow_nonpos hL'neg diff.totalDegree
              simp [u, max_eq_left hLe_neg]
            · have hbx' : 0 ≤ σx * (z 0 - (x₀ - σx * δ)) := by
                have : σx * (z 0 - (x₀ - σx * δ)) = σx * (z 0 - x₀) + (σx * σx) * δ := by ring
                rw [this, hσx, one_mul]; linarith [hbx z hz]
              have hL'δ : δ ≤ MvPolynomial.eval z L' := by
                rw [hL'_eq z]
                have : σx * (z 0 - (x₀ - σx * δ)) = σx * (z 0 - x₀) + (σx * σx) * δ := by ring
                rw [this, hσx, one_mul]; linarith [hbx z hz, hby z hz]
              have h1 := hC z hbx' (hby z hz).le (by
                have heqL : MvPolynomial.eval z
                    (MvPolynomial.C σx * (MvPolynomial.X 0 - MvPolynomial.C (x₀ - σx * δ)) +
                     MvPolynomial.C σy * (MvPolynomial.X 1 - MvPolynomial.C y₀)) = MvPolynomial.eval z L' := by
                  rw [hL'_eq z]; simp
                rwa [heqL])
              have heqL : MvPolynomial.eval z
                  (MvPolynomial.C σx * (MvPolynomial.X 0 - MvPolynomial.C (x₀ - σx * δ)) +
                   MvPolynomial.C σy * (MvPolynomial.X 1 - MvPolynomial.C y₀)) = MvPolynomial.eval z L' := by
                rw [hL'_eq z]; simp
              rw [heqL] at h1
              simp only [diff, map_sub] at h1
              have h2 := mul_le_mul_of_nonneg_left (le_max_right 0 ((MvPolynomial.eval z L') ^ e)) hC_nn
              dsimp only [u]; linarith
  choose uSep huSep_SI huSep_le huSep_ge using hpair
  -- Step 5: Assemble F = sup_b inf_a uSep a b ∈ SI and show F = f on the dense set ⋃ E idx.
  let uB : CellIdx → (Fin 2 → ℝ) → ℝ := fun b z =>
    Finset.univ.inf' Finset.univ_nonempty (fun a : CellIdx => uSep a b z)
  have huB_SI : ∀ b, SI (uB b) := fun b =>
    SI_finset_inf' Finset.univ_nonempty _ (fun a _ => huSep_SI a b)
  let F : (Fin 2 → ℝ) → ℝ := fun z =>
    Finset.univ.sup' Finset.univ_nonempty (fun b : CellIdx => uB b z)
  have hF_SI : SI F := SI_finset_sup' Finset.univ_nonempty _ (fun b _ => huB_SI b)
  have hF_eq_cell : ∀ (idx : CellIdx) (z : Fin 2 → ℝ), z ∈ E idx → F z = f z := by
    intro idx z hz
    rw [hE_val idx z hz]
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro b _
      exact (Finset.inf'_le (fun a => uSep a b z) (Finset.mem_univ idx)).trans (huSep_le idx b z hz)
    · refine le_trans ?_ (Finset.le_sup' (fun b => uB b z) (Finset.mem_univ idx))
      rw [Finset.le_inf'_iff]
      intro a _
      exact huSep_ge a idx z hz
  -- Show ⋃ idx, E idx is dense in Fin 2 → ℝ, hence F = f everywhere!
  have hF_eq : F = f := by
    funext z
    by_contra hne
    let δ := |F z - f z| / 2
    have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hne))
    obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp ((SI_continuous hF_SI).sub hf_cont).continuousAt δ hδ
    -- Pick y' ∈ (z 1 - ε, z 1 + ε) \ CritY
    have hy'_ex : (Set.Ioo (z 1 - ε) (z 1 + ε) \ ↑CritY).Nonempty :=
      ((Set.Ioo_infinite (by linarith : z 1 - ε < z 1 + ε)).diff (Finset.finite_toSet _)).nonempty
    obtain ⟨y', hy'_Ioo, hy'_not⟩ := hy'_ex
    obtain ⟨q, hq⟩ := critInterval_cover CritY y' (fun h => hy'_not (Finset.mem_coe.mpr h))
    -- Pick x' ∈ (z 0 - ε, z 0 + ε) \ {ζH q k y' | k}
    have hx'_ex : (Set.Ioo (z 0 - ε) (z 0 + ε) \ ↑(Finset.univ.image fun k : Fin (sH q) => ζH q k y')).Nonempty :=
      ((Set.Ioo_infinite (by linarith : z 0 - ε < z 0 + ε)).diff (Finset.finite_toSet _)).nonempty
    obtain ⟨x', hx'_Ioo, hx'_not⟩ := hx'_ex
    have hx'_nζ : ∀ k : Fin (sH q), x' ≠ ζH q k y' := fun k heq' =>
      hx'_not (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, heq'.symm⟩))
    let S_lt : Finset (Fin (sH q)) := Finset.univ.filter fun k => ζH q k y' < x'
    have hcell_ex : ∃ k : Fin (sH q + 1), (fun i => if i = 0 then x' else y') ∈ E ⟨q, k⟩ := by
      by_cases hsne : S_lt.Nonempty
      · let k0 := S_lt.max' hsne
        have hk0_lt : ζH q k0 y' < x' := (Finset.mem_filter.mp (Finset.max'_mem S_lt hsne)).2
        refine ⟨⟨k0.val + 1, by omega⟩, hq, fun _ => ?_, fun h => ?_⟩
        · have heq' : (⟨k0.val + 1 - 1, by omega⟩ : Fin (sH q)) = k0 := by ext; simp
          simpa [sw, heq'] using hk0_lt
        · by_contra hle
          have hlt' : ζH q ⟨k0.val + 1, h⟩ y' < x' :=
            lt_of_le_of_ne (not_lt.mp (by simpa [sw] using hle)) (hx'_nζ _).symm
          have hin : ⟨k0.val + 1, h⟩ ∈ S_lt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩
          have hle' : (⟨k0.val + 1, h⟩ : Fin (sH q)) ≤ k0 := Finset.le_max' S_lt ⟨k0.val + 1, h⟩ hin
          have hle'' : k0.val + 1 ≤ k0.val := hle'
          omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hsne
        refine ⟨⟨0, by omega⟩, hq, fun h => False.elim (Nat.not_lt_zero _ h), fun h => ?_⟩
        by_contra hle
        have hlt' : ζH q ⟨0, h⟩ y' < x' :=
          lt_of_le_of_ne (not_lt.mp (by simpa [sw] using hle)) (hx'_nζ _).symm
        have : ⟨0, h⟩ ∈ S_lt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩
        rw [hsne] at this; exact False.elim (Finset.notMem_empty _ this)
    obtain ⟨k, hk⟩ := hcell_ex
    let w : Fin 2 → ℝ := fun i => if i = 0 then x' else y'
    have hdist : dist w z < ε := by
      rw [dist_pi_lt_iff hε]
      intro i; fin_cases i
      · change |x' - z 0| < ε
        rw [abs_lt]; constructor <;> linarith [hx'_Ioo.1, hx'_Ioo.2]
      · change |y' - z 1| < ε
        rw [abs_lt]; constructor <;> linarith [hy'_Ioo.1, hy'_Ioo.2]
    have hlt := hball hdist
    have heq_w : F w = f w := hF_eq_cell ⟨q, k⟩ w hk
    rw [Real.dist_eq, Pi.sub_apply, Pi.sub_apply, heq_w, sub_self, zero_sub, abs_neg] at hlt
    change |F z - f z| < |F z - f z| / 2 at hlt
    linarith [abs_nonneg (F z - f z)]
  rwa [← hF_eq]

end OMAPB2

theorem OMA.solution : type_of% @PierceBirkhoff.pierce_birkhoff_conjecture_dim_two := by
  intro f hf
  obtain ⟨ι, κ, _, _, _, _, g, hg⟩ := OMAPB2.pierce_birkhoff_dim_two_SI f hf
  exact ⟨ι, κ, g, inferInstance, inferInstance, hg⟩
