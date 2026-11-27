import FormalConjectures.ErdosProblems.«40»

/-!
# The weaker variant of Erdős Problem 40

Compactness identifies the existence of a diverging denominator with the general
Erdős–Turán conjecture at square-root density. A finite criterion expresses this
using only subsets of a finite interval and integer inequalities. The final theorem
reduces the density problem to the four-representation case and a thinning step.

Credit: @NicholasWierenga
-/

open AdditiveCombinatorics Filter Real Set

namespace OMA.R_Erdos40_erdos_40_variants_weaker_R1

theorem global_cap_of_limsup_ne_top (A : Set ℕ)
    (h : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤) :
    ∃ k : ℕ, ∀ n, sumRep A n ≤ k := by
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp h
  have hlt : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop < ((b + 1 : ℕ) : ℕ∞) := by
    rw [← hb]
    exact_mod_cast Nat.lt_succ_self b
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_limsup_lt hlt)
  refine ⟨max b ((Finset.range N).sup (sumRep A)), fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · have hb' : sumRep A n < b + 1 := by exact_mod_cast hN n hn
    exact (Nat.le_of_lt_succ hb').trans (le_max_left _ _)
  · exact (Finset.le_sup (f := sumRep A) (Finset.mem_range.mpr (by omega : n < N))).trans
      (le_max_right _ _)

theorem small_prefix (h : Erdos40.Erdos40For (fun _ ↦ 1)) (k : ℕ) (A : Set ℕ)
    (hcap : ∀ n, sumRep A n ≤ k) (L : ℕ) :
    ∃ n, L ≤ n ∧ (k : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < √(n : ℝ) := by
  by_contra! hnone
  have htop := h A (Asymptotics.IsBigO.of_bound ((k : ℝ)^2) (by
    filter_upwards [eventually_ge_atTop L] with n hn
    simpa only [div_one, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast]
      using hnone n hn))
  have hle : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≤ (k : ℕ∞) :=
    limsup_le_of_le (h := Eventually.of_forall (fun n ↦ by exact_mod_cast hcap n))
  rw [htop] at hle
  exact (ENat.natCast_lt_top k).not_ge hle

theorem constant_one_of_witness {g : ℕ → ℝ} (hg : Tendsto g atTop atTop)
    (h : Erdos40.Erdos40For g) : Erdos40.Erdos40For (fun _ ↦ 1) := by
  intro A hA
  apply h A
  apply Asymptotics.IsBigO.trans _ hA
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [hg.eventually_ge_atTop 1] with n hn
  simpa only [div_one, one_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one hn))]
    using div_le_self (Real.sqrt_nonneg (n : ℝ)) hn

/-- A predicate determined by a finite prefix defines an open set of Boolean sequences. -/
theorem isOpen_prefix {P : (ℕ → Bool) → Prop} (n : ℕ)
    (hP : ∀ f g, (∀ i ≤ n, f i = g i) → (P f ↔ P g)) :
    IsOpen {f | P f} := by
  refine isOpen_pi_iff.mpr ?_
  intro f hf
  refine ⟨Finset.range (n + 1), fun i ↦ {f i}, fun i _ ↦ ⟨isOpen_discrete _, by simp⟩, ?_⟩
  intro g hg
  apply (hP f g ?_).mp hf
  intro i hi
  have hi' : i ∈ (↑(Finset.range (n + 1)) : Set ℕ) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact (Set.mem_singleton_iff.mp (Set.mem_pi.mp hg i hi')).symm

theorem sumRep_decode_congr {f g : ℕ → Bool} {n : ℕ}
    (h : ∀ i ≤ n, f i = g i) : sumRep (({i : ℕ | f i = true} : Set ℕ)) n = sumRep (({i : ℕ | g i = true} : Set ℕ)) n := by
  classical
  simp only [sumRep_def]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  by_cases hp : p ∈ _root_.Finset.HasAntidiagonal.antidiagonal n
  · have hsum := _root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hleft : p.1 ≤ n := by omega
    have hright : p.2 ≤ n := by omega
    simp only [hp, true_and]
    change (f p.1 = true ∧ f p.2 = true) ↔ (g p.1 = true ∧ g p.2 = true)
    rw [h _ hleft, h _ hright]
  · simp [hp]

theorem count_decode_congr {f g : ℕ → Bool} {n : ℕ}
    (h : ∀ i ≤ n, f i = g i) :
    (({i : ℕ | f i = true} : Set ℕ) ∩ Icc 1 n).ncard = (({i : ℕ | g i = true} : Set ℕ) ∩ Icc 1 n).ncard := by
  have he : ({i : ℕ | f i = true} : Set ℕ) ∩ Icc 1 n = ({i : ℕ | g i = true} : Set ℕ) ∩ Icc 1 n := by
    ext i
    change (f i = true ∧ (1 ≤ i ∧ i ≤ n)) ↔ (g i = true ∧ (1 ≤ i ∧ i ≤ n))
    by_cases hi : i ≤ n
    · rw [h _ hi]
    · simp [hi]
  rw [he]

/-- Compactness makes the upper endpoint of the density failure window independent of the set. -/
theorem uniform_window (k L : ℕ)
    (hbad : ∀ A : Set ℕ, (∀ n, sumRep A n ≤ k) → ∀ l : ℕ,
      ∃ n, l ≤ n ∧ (k : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < Real.sqrt (n : ℝ)) :
    ∃ U : ℕ, ∀ A : Set ℕ, (∀ n, sumRep A n ≤ k) →
      ∃ n, L ≤ n ∧ n ≤ U ∧
        (k : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < Real.sqrt (n : ℝ) := by
  classical
  let K : Set (ℕ → Bool) := {f | ∀ n, sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k}
  have hK : IsCompact K := by
    apply IsClosed.isCompact
    have he : K = ⋂ n : ℕ, {f | sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k} := by
      ext f
      simp only [K, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [he]
    apply isClosed_iInter
    intro n
    apply isOpen_compl_iff.mp
    exact isOpen_prefix n fun f g h ↦ by
      change (¬ sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k) ↔ (¬ sumRep (({i : ℕ | g i = true} : Set ℕ)) n ≤ k)
      rw [sumRep_decode_congr h]
  let V : {n : ℕ // L ≤ n} → Set (ℕ → Bool) := fun n ↦
    {f | (k : ℝ)^2 * ((({i : ℕ | f i = true} : Set ℕ) ∩ Icc 1 n.val).ncard : ℝ) < Real.sqrt (n.val : ℝ)}
  have hV : ∀ n, IsOpen (V n) := by
    intro n
    apply isOpen_prefix n.val
    intro f g h
    rw [count_decode_congr h]
  have hcover : K ⊆ ⋃ n, V n := by
    intro f hf
    change ∀ n, sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k at hf
    obtain ⟨n, hn, hfail⟩ := hbad (({i : ℕ | f i = true} : Set ℕ)) hf L
    exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, hfail⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV hcover
  refine ⟨s.sup Subtype.val, ?_⟩
  intro A hA
  let f : ℕ → Bool := fun i ↦ decide (i ∈ A)
  have hf : ({i : ℕ | f i = true} : Set ℕ) = A := by
    ext i
    exact decide_eq_true_iff
  have hfK : f ∈ K := by
    change ∀ n, sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k
    simpa only [hf] using hA
  obtain ⟨n, hn, hfail⟩ := Set.mem_iUnion₂.mp (hs hfK)
  refine ⟨n.val, n.property, Finset.le_sup (f := Subtype.val) hn, ?_⟩
  change (k : ℝ)^2 * ((({i : ℕ | f i = true} : Set ℕ) ∩ Icc 1 n.val).ncard : ℝ) < Real.sqrt (n.val : ℝ) at hfail
  simpa only [hf] using hfail

/-- Uniform finite windows of low density give a single diverging witness function. -/
theorem diagonalWitness
    (hw : ∀ k L : ℕ, 0 < k → ∃ U : ℕ, ∀ A : Set ℕ,
      (∀ n, sumRep A n ≤ k) →
      ∃ n, L ≤ n ∧ n ≤ U ∧
        (k : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < Real.sqrt (n : ℝ))
    (hcap : ∀ A : Set ℕ,
      (limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤) →
      ∃ k : ℕ, ∀ n, sumRep A n ≤ k) :
    ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g := by
  classical
  choose U hU using fun j : ℕ => hw (j + 1) j (Nat.succ_pos j)
  -- The first window endpoint reaching n supplies its index.
  let endpoint (j : ℕ) := max j (U j)
  have reaches (n : ℕ) : ∃ j, n ≤ endpoint j := ⟨n, le_max_left _ _⟩
  let index (n : ℕ) := Nat.find (reaches n)
  let g (n : ℕ) : ℝ := (↑(index n + 1) : ℝ)
  have hgpos (n : ℕ) : 0 < g n := by
    dsimp [g]
    positivity
  refine ⟨g, ?_, ?_⟩
  · refine tendsto_atTop.2 fun x => ?_
    obtain ⟨j, hj⟩ := exists_nat_ge x
    filter_upwards [eventually_ge_atTop ((Finset.range j).sup endpoint + 1)] with n hn
    have hindex : j ≤ index n := by
      by_contra! hlt
      have hn' : n ≤ endpoint (index n) := Nat.find_spec (reaches n)
      have hend : endpoint (index n) ≤ (Finset.range j).sup endpoint :=
        Finset.le_sup (Finset.mem_range.mpr hlt)
      omega
    have hcast : (j : ℝ) ≤ g n := by
      dsimp [g]
      exact_mod_cast (show j ≤ index n + 1 by omega)
    exact hj.trans hcast
  · intro A hbigO
    by_contra hr
    obtain ⟨k, hk⟩ := hcap A hr
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hbigO
    obtain ⟨L, hL⟩ := eventually_atTop.mp hC
    obtain ⟨c, hc⟩ := exists_nat_ge C
    let j := max k (max c L)
    have hkj : k ≤ j + 1 := by
      have : k ≤ j := le_max_left _ _
      omega
    have hcj : C ≤ (↑(j + 1) : ℝ) := by
      apply hc.trans
      have : c ≤ j := (le_max_left c L).trans (le_max_right k _)
      exact_mod_cast (show c ≤ j + 1 by omega)
    have hLj : L ≤ j := (le_max_right c L).trans (le_max_right k _)
    obtain ⟨n, hjn, hnU, hsmall⟩ := hU j A (fun n => (hk n).trans hkj)
    have hind : index n ≤ j :=
      Nat.find_min' (reaches n) (hnU.trans (le_max_right _ _))
    have hgj : g n ≤ (↑(j + 1) : ℝ) := by
      dsimp [g]
      exact_mod_cast (Nat.succ_le_succ hind)
    let a : ℝ := ((A ∩ Icc 1 n).ncard : ℝ)
    have ha : 0 ≤ a := by
      dsimp [a]
      positivity
    have hbound := hL n (hLj.trans hjn)
    change ‖Real.sqrt (n : ℝ) / g n‖ ≤ C * ‖a‖ at hbound
    rw [Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (hgpos n).le),
      Real.norm_of_nonneg ha] at hbound
    have hcoeff : C * g n ≤ (↑(j + 1) : ℝ)^2 := by
      rw [pow_two]
      exact (mul_le_mul_of_nonneg_right hcj (hgpos n).le).trans
        (mul_le_mul_of_nonneg_left hgj (Nat.cast_nonneg _))
    have hsqrt : Real.sqrt (n : ℝ) ≤ (↑(j + 1) : ℝ)^2 * a := by
      calc
        Real.sqrt (n : ℝ) ≤ (C * a) * g n := (div_le_iff₀ (hgpos n)).mp hbound
        _ = (C * g n) * a := by ring
        _ ≤ (↑(j + 1) : ℝ)^2 * a := mul_le_mul_of_nonneg_right hcoeff ha
    exact (not_lt_of_ge hsqrt) hsmall

/-- A single diverging denominator exists exactly when square-root lower density
forces unbounded two-sum representations. -/
theorem weaker_iff_constant_one :
    (∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g) ↔
      Erdos40.Erdos40For (fun _ ↦ 1) := by
  constructor
  · rintro ⟨g, hg, h⟩
    exact constant_one_of_witness hg h
  · intro h
    apply diagonalWitness _ global_cap_of_limsup_ne_top
    intro k L _
    exact uniform_window k L (small_prefix h k)

theorem sumRep_mono_set {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    sumRep A n ≤ sumRep B n := by
  classical
  rw [sumRep_def, sumRep_def]
  apply Finset.card_le_card
  apply Finset.monotone_filter_right
  intro p _ hp
  exact ⟨h hp.1, h hp.2⟩

theorem sumRep_trunc_zero {B : Set ℕ} {U n : ℕ} (hB : B ⊆ Set.Iic U)
    (hn : 2 * U < n) : sumRep B n = 0 := by
  classical
  rw [sumRep_def]
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro p hp hpair
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hfirst := Set.mem_Iic.mp (hB hpair.1)
  have hsecond := Set.mem_Iic.mp (hB hpair.2)
  omega

theorem prefix_count_trunc (A : Set ℕ) {n U : ℕ} (h : n ≤ U) :
    ((A ∩ Set.Iic U) ∩ Set.Icc 1 n).ncard = (A ∩ Set.Icc 1 n).ncard := by
  have hprefix : (A ∩ Set.Iic U) ∩ Set.Icc 1 n = A ∩ Set.Icc 1 n := by
    ext x
    constructor
    · rintro ⟨⟨hxA, _⟩, hx⟩
      exact ⟨hxA, hx⟩
    · rintro ⟨hxA, hx⟩
      exact ⟨⟨hxA, (Set.mem_Icc.mp hx).2.trans h⟩, hx⟩
  rw [hprefix]

theorem sqrt_bound_iff_nat (k c n : ℕ) :
    ((k : ℝ)^2 * (c : ℝ) < √(n : ℝ)) ↔ (k^2 * c)^2 < n := by
  rw [Real.lt_sqrt (by positivity : 0 ≤ (k : ℝ)^2 * (c : ℝ))]
  norm_cast

theorem finite_prefix_count (B : Finset ℕ) (n : ℕ) :
    ((B : Set ℕ) ∩ Icc 1 n).ncard = (B.filter (fun x ↦ 1 ≤ x ∧ x ≤ n)).card := by
  have heq : (B : Set ℕ) ∩ Icc 1 n = (↑(B.filter (fun x ↦ 1 ≤ x ∧ x ≤ n)) : Set ℕ) := by
    ext x
    simp
  rw [heq, Set.ncard_coe_finset]

theorem window_of_finite_certificate {k d L U : ℕ}
    (hU : ∀ B ∈ (Finset.range (U + 1)).powerset,
        (∀ s ∈ Finset.range (2 * U + 1), ((_root_.Finset.HasAntidiagonal.antidiagonal s).filter
          (fun p ↦ p.1 ∈ B ∧ p.2 ∈ B)).card ≤ k) →
        ∃ n ∈ Finset.Icc L U,
          (d^2 * (B.filter (fun x ↦ 1 ≤ x ∧ x ≤ n)).card)^2 < n)
    (A : Set ℕ) (hcap : ∀ n, sumRep A n ≤ k) :
    ∃ n, L ≤ n ∧ n ≤ U ∧ (d : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < √(n : ℝ) := by
  classical
  let B := (Finset.range (U + 1)).filter (· ∈ A)
  have hBA : (B : Set ℕ) ⊆ A := fun _ hx ↦ (Finset.mem_filter.mp hx).2
  have hBeq : (B : Set ℕ) = A ∩ Iic U := by
    ext x
    simp only [B, Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
      Nat.lt_succ_iff, Set.mem_inter_iff, Set.mem_Iic, and_comm]
  obtain ⟨n, hnMem, hn⟩ := hU B (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
    (fun s _ ↦ by simpa only [sumRep_def, Finset.mem_coe] using
      (sumRep_mono_set hBA s).trans (hcap s))
  obtain ⟨hnL, hnU⟩ := Finset.mem_Icc.mp hnMem
  have hsmall := (sqrt_bound_iff_nat _ _ _).mpr hn
  rw [← finite_prefix_count, hBeq, prefix_count_trunc A hnU] at hsmall
  exact ⟨n, hnL, hnU, hsmall⟩

/-- The quantifiers following each proposed upper endpoint range only over finite
data. This is an exact finite obstruction criterion for the existential variant. -/
theorem weaker_iff_finite_windows :
    (∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g) ↔
      ∀ k L : ℕ, 0 < k → ∃ U : ℕ, ∀ B ∈ (Finset.range (U + 1)).powerset,
        (∀ s ∈ Finset.range (2 * U + 1), ((_root_.Finset.HasAntidiagonal.antidiagonal s).filter
          (fun p ↦ p.1 ∈ B ∧ p.2 ∈ B)).card ≤ k) →
        ∃ n ∈ Finset.Icc L U,
          (k^2 * (B.filter (fun x ↦ 1 ≤ x ∧ x ≤ n)).card)^2 < n := by
  classical
  constructor
  · intro h k L _
    obtain ⟨U, hU⟩ := uniform_window k L (small_prefix (weaker_iff_constant_one.mp h) k)
    refine ⟨U, fun B hB hcap ↦ ?_⟩
    have hBU : (B : Set ℕ) ⊆ Iic U := fun n hn ↦
      Nat.le_of_lt_succ (Finset.mem_range.mp ((Finset.mem_powerset.mp hB) hn))
    have hglobal (s : ℕ) : sumRep (B : Set ℕ) s ≤ k := by
      by_cases hs : s ≤ 2 * U
      · simpa only [sumRep_def, Finset.mem_coe] using hcap s (Finset.mem_range.mpr (Nat.lt_succ_of_le hs))
      · rw [sumRep_trunc_zero hBU (lt_of_not_ge hs)]
        exact Nat.zero_le _
    obtain ⟨n, hnL, hnU, hsmall⟩ := hU (B : Set ℕ) hglobal
    rw [finite_prefix_count] at hsmall
    exact ⟨n, Finset.mem_Icc.mpr ⟨hnL, hnU⟩, (sqrt_bound_iff_nat _ _ _).mp hsmall⟩
  · intro hf
    apply diagonalWitness _ global_cap_of_limsup_ne_top
    intro k L hk
    obtain ⟨U, hU⟩ := hf k L hk
    refine ⟨U, fun A hcap ↦ ?_⟩
    exact window_of_finite_certificate hU A hcap

/-- Find finite obstruction intervals at the four-representation bound.
Every proposed endpoint can be checked by finite integer arithmetic. -/
def H1 : Prop :=
  ∀ d L : ℕ, 0 < d → ∃ U : ℕ, ∀ B ∈ (Finset.range (U + 1)).powerset,
    (∀ s ∈ Finset.range (2 * U + 1), ((_root_.Finset.HasAntidiagonal.antidiagonal s).filter
      (fun p ↦ p.1 ∈ B ∧ p.2 ∈ B)).card ≤ 4) →
    ∃ n ∈ Finset.Icc L U, (d^2 * (B.filter (fun x ↦ 1 ≤ x ∧ x ≤ n)).card)^2 < n

/-- A thinning step. Lower the ordered representation bound by one while
retaining a positive square-root lower density. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ A : Set ℕ, (∀ n, sumRep A n ≤ k + 1) →
    ((fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
        (fun n ↦ ((A ∩ Icc 1 n).ncard : ℝ))) →
    ∃ B : Set ℕ, B ⊆ A ∧ (∀ n, sumRep B n ≤ k) ∧
      ((fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
        (fun n ↦ ((B ∩ Icc 1 n).ncard : ℝ)))

theorem four_bound_sparse (hfour : H1) (A : Set ℕ) (hcap : ∀ n, sumRep A n ≤ 4) :
    ¬ ((fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
        (fun n ↦ ((A ∩ Icc 1 n).ncard : ℝ))) := by
  intro hdense
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hdense
  obtain ⟨L, hL⟩ := eventually_atTop.mp hC
  obtain ⟨d, hd⟩ := exists_nat_ge C
  obtain ⟨U, hU⟩ := hfour (d + 1) L (Nat.succ_pos d)
  obtain ⟨n, hn, _, hsmall⟩ := window_of_finite_certificate hU A hcap
  have hlarge := hL n hn
  simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast] at hlarge
  have hcoeff : C ≤ ((d + 1 : ℕ) : ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg (d : ℝ), Nat.cast_nonneg (α := ℝ) d]
  exact hsmall.not_ge (hlarge.trans (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)))

theorem main : H1 → H2 → type_of% @Erdos40.erdos_40.variants.weaker := by
  intro hfour hthin
  have hsparse : ∀ k : ℕ, ∀ A : Set ℕ, (∀ n, sumRep A n ≤ k) →
      ¬ ((fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
        (fun n ↦ ((A ∩ Icc 1 n).ncard : ℝ))) := by
    intro k
    induction k with
    | zero =>
      intro A hA
      exact four_bound_sparse hfour A (fun n ↦ (hA n).trans (by decide))
    | succ k ih =>
      intro A hA hdense
      by_cases hk : 4 ≤ k
      · obtain ⟨B, _, hB, hdB⟩ := hthin k hk A hA hdense
        exact ih B hB hdB
      · exact four_bound_sparse hfour A (fun n ↦ (hA n).trans (by omega)) hdense
  apply weaker_iff_constant_one.mpr
  intro A hA
  by_contra hbound
  obtain ⟨k, hk⟩ := global_cap_of_limsup_ne_top A hbound
  exact hsparse k A hk (by simpa only [div_one] using hA)

end OMA.R_Erdos40_erdos_40_variants_weaker_R1
