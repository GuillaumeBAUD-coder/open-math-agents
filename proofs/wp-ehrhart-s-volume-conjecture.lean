import OMAStatements.S_wp_ehrhart_s_volume_conjecture

-- Problem: Ehrhart's volume conjecture.
-- The proof uses the finite-field jet and prime-crossing strategy of Initio,
-- with an indicator polynomial in place of the finite group algebra.
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology
namespace EhrhartAdapt
open Finset

section
variable {F I : Type*} [Field F] [Fintype I] [LinearOrder I]

def Pivot (W : Submodule F (I → F)) (i : I) : Prop :=
  ∃ v ∈ W, v i = 1 ∧ ∀ j < i, v j = 0

lemma finrank_le_pivot (W : Submodule F (I → F)) [Fintype {i // Pivot W i}] :
    Module.finrank F W ≤ Fintype.card {i // Pivot W i} := by
  classical
  let L : W →ₗ[F] ({i // Pivot W i} → F) :=
    { toFun := fun v i => v.1 i.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    change L v = 0 at hv
    apply Subtype.ext
    by_contra h
    have hn : ∃ i, v.1 i ≠ 0 := by
      by_contra! hn
      exact h (funext hn)
    let s := univ.filter (fun i => v.1 i ≠ 0)
    have hs : s.Nonempty := by simpa [s, Finset.Nonempty] using hn
    let i := s.min' hs
    have hvi : v.1 i ≠ 0 := (mem_filter.mp (min'_mem s hs)).2
    have hprev (j : I) (hj : j < i) : v.1 j = 0 := by
      by_contra hj0
      exact (not_le_of_gt hj) (min'_le s j (mem_filter.mpr ⟨mem_univ _, hj0⟩))
    have hp : Pivot W i := by
      refine ⟨(v.1 i)⁻¹ • v.1, W.smul_mem _ v.2, ?_, ?_⟩
      · simp [Pi.smul_apply, hvi]
      · intro j hj
        simp [Pi.smul_apply, hprev j hj]
    exact hvi (congrFun hv ⟨i, hp⟩)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

lemma depth_flags (W : ℕ → Submodule F (I → F)) (h0 : W 0 = ⊤) (M : ℕ) :
    ∃ (d : I → ℕ) (c : I → I → F), (∀ i, d i ≤ M) ∧
      (∀ i, c i ∈ W (d i) ∧ c i i = 1 ∧ ∀ j < i, c i j = 0) ∧
      (∀ r : ℕ, r ≤ M → Module.finrank F (W r) ≤ (univ.filter (fun i => r ≤ d i)).card) := by
  classical
  let s (i : I) := (range (M+1)).filter (fun r => Pivot (W r) i)
  have hn (i : I) : (s i).Nonempty := by
    refine ⟨0, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩⟩
    rw [h0]
    refine ⟨Pi.single i 1, Submodule.mem_top, by simp, ?_⟩
    intro j hj
    simp [Pi.single_eq_of_ne (ne_of_lt hj)]
  let d (i : I) := (s i).max' (hn i)
  have hd (i : I) : d i ∈ s i := max'_mem _ _
  choose c hc using fun i => (mem_filter.mp (hd i)).2
  refine ⟨d, c, fun i => Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp (hd i)).1), hc, ?_⟩
  intro r hr
  let e : {i // Pivot (W r) i} → {i // i ∈ univ.filter (fun i => r ≤ d i)} := fun i =>
    ⟨i.1, mem_filter.mpr ⟨mem_univ _, le_max' _ _ (mem_filter.mpr ⟨mem_range.mpr (by omega), i.2⟩)⟩⟩
  have hcr : Fintype.card {i // Pivot (W r) i} ≤ (univ.filter (fun i => r ≤ d i)).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_le_of_injective e
    intro i j hij
    exact Subtype.ext (congrArg (fun v : {i // i ∈ univ.filter (fun i => r ≤ d i)} => v.1) hij)
  exact (finrank_le_pivot (W r)).trans hcr
end

lemma poly_annihilate {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (a : I → J → F) (c : I → I → F) (d : I → ℕ)
    (hc : ∀ i (m : J → ℕ), (∑ j, m j) < d i → (∑ l, c i l * ∏ j, a l j ^ m j) = 0)
    (P : MvPolynomial (I × J) F) (hp : P.totalDegree < ∑ i, d i) :
    (∑ f : I → I, (∏ i, c i (f i)) * MvPolynomial.eval (fun ij => a (f ij.1) ij.2) P) = 0 := by
  classical
  simp_rw [MvPolynomial.eval_eq', mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro m hm
  have hmd := MvPolynomial.le_totalDegree hm |>.trans_lt hp
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type] at hmd
  have hi : ∃ i, (∑ j, m (i,j)) < d i := by
    by_contra! h
    exact (not_le_of_gt hmd) (sum_le_sum fun i _ => h i)
  obtain ⟨i, hi⟩ := hi
  have hs (f : I → I) : ((∏ i, c i (f i)) *
      (P.coeff m * ∏ ij : I × J, a (f ij.1) ij.2 ^ m ij)) =
      P.coeff m * ∏ i, (c i (f i) * ∏ j, a (f i) j ^ m (i,j)) := by
    rw [prod_mul_distrib, Fintype.prod_prod_type]
    ring
  simp_rw [hs]
  rw [← mul_sum, ← Fintype.prod_sum (fun (i l : I) => c i l * ∏ j, a l j ^ m (i,j))]
  rw [prod_eq_zero (mem_univ i) (hc i (fun j => m (i,j)) hi), mul_zero]

lemma row_bound {I J : Type*} [Fintype I] [Fintype J] [LinearOrder I]
    {p : ℕ} [Fact p.Prime]
    (a : I → J → ZMod p) (c : I → I → ZMod p) (d : I → ℕ)
    (hc : ∀ i (m : J → ℕ), (∑ j, m j) < d i → (∑ l, c i l * ∏ j, a l j ^ m j) = 0)
    (hd : ∀ i, c i i = 1) (htri : ∀ i j, j < i → c i j = 0)
    (hsep : ∀ f : I → I, (∀ i, i ≤ f i) →
      (∀ j, ∑ i, a (f i) j = ∑ i, a i j) → f = id) :
    ∑ i, d i ≤ Fintype.card J * (p - 1) := by
  classical
  let Q (j : J) : MvPolynomial (I × J) (ZMod p) :=
    (∑ i : I, MvPolynomial.X (i,j)) - MvPolynomial.C (∑ i, a i j)
  let R (j : J) : MvPolynomial (I × J) (ZMod p) := 1 - Q j ^ (p-1)
  let P := ∏ j, R j
  have hQ (j : J) : (Q j).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ (by rw [MvPolynomial.totalDegree_C]; omega))
    exact MvPolynomial.totalDegree_finsetSum_le (fun i _ => by simp)
  have hR (j : J) : (R j).totalDegree ≤ p-1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) ?_)
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (p-1) (hQ j))
  have hP : P.totalDegree ≤ Fintype.card J * (p-1) :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans (by simpa using sum_le_sum (s := (univ : Finset J)) (fun j _ => hR j))
  by_contra! h
  have hvan := poly_annihilate a c d hc P (hP.trans_lt h)
  rw [sum_eq_single id] at hvan
  · have hpp : MvPolynomial.eval (fun ij : I × J => a ij.1 ij.2) P = 1 := by
      have hp : p-1 ≠ 0 := Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt
      simp [P, R, Q, map_prod, map_pow, map_sub, map_sum, hp]
    simp [hd, hpp] at hvan
  · intro f hf hfi
    by_cases hge : ∀ i, i ≤ f i
    · have hex : ∃ j, (∑ i, a (f i) j) ≠ ∑ i, a i j := by
        by_contra! hh
        exact hfi (hsep f hge hh)
      obtain ⟨j, hj⟩ := hex
      have hpp : MvPolynomial.eval (fun ij : I × J => a (f ij.1) ij.2) P = 0 := by
        rw [show P = ∏ j, R j from rfl, map_prod]
        apply prod_eq_zero (mem_univ j)
        simp [R, Q, map_sub, map_pow, map_sum, ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hj)]
      rw [hpp, mul_zero]
    · push Not at hge
      obtain ⟨i, hi⟩ := hge
      rw [prod_eq_zero (mem_univ i) (htri i (f i) hi), zero_mul]
  · simp

noncomputable def Jets (n q : ℕ) := {m : Fin n → ℕ // (∑ j, m j) ≤ q}
noncomputable instance (n q : ℕ) : Fintype (Jets n q) :=
  Fintype.ofInjective (fun m : Jets n q => fun j => (⟨m.1 j, Nat.lt_succ_of_le ((single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)).trans m.2)⟩ : Fin (q+1)))
    (fun _ _ h => Subtype.ext (funext fun j => congrArg Fin.val (congrFun h j)))

lemma card_jets (n q : ℕ) : Fintype.card (Jets n q) = (n+q).choose n := by
  classical
  let e : Jets n q ≃ {m : Fin (n + 1) → ℕ // (∑ i, m i) = q} :=
    { toFun := fun m => ⟨Fin.cons (q - ∑ j, m.1 j) m.1, by rw [Fin.sum_univ_succ]; simp [Nat.sub_add_cancel m.2]⟩
      invFun := fun m => ⟨fun j => m.1 j.succ, by
        have h := m.2
        rw [Fin.sum_univ_succ] at h
        change (∑ j : Fin n, m.1 j.succ) ≤ q
        omega⟩
      left_inv := by intro m; apply Subtype.ext; funext j; simp
      right_inv := by
        intro m
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have h := m.2
          rw [Fin.sum_univ_succ] at h
          simp only [Fin.cons_zero]
          omega
        · simp }
  rw [Fintype.card_congr (e.trans (Sym.equivNatSumOfFintype _ _).symm), Sym.card_sym_eq_choose, Fintype.card_fin]
  rw [show n+1+q-1 = n+q by omega, ← Nat.choose_symm (by omega : q ≤ n+q)]
  rw [show n+q-q=n by omega]

lemma hockey (n M : ℕ) : ∑ r ∈ range M, (n+r).choose n = (n+M).choose (n+1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [sum_range_succ, ih, ← Nat.add_assoc, Nat.choose_succ_succ, add_comm]

lemma sum_card_depth {I : Type*} [Fintype I] (M : ℕ) (d : I → ℕ) (hd : ∀ i, d i ≤ M) :
    ∑ r ∈ range M, (univ.filter (fun i => r+1 ≤ d i)).card = ∑ i, d i := by
  classical
  have h (r : ℕ) : (univ.filter (fun i => r+1 ≤ d i)).card = ∑ i, (if r+1 ≤ d i then 1 else 0) :=
    (sum_boole (R := ℕ) _ _).symm
  simp_rw [h]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have he : (range M).filter (fun x => x+1 ≤ d i) = range (d i) := by
    ext x
    simp only [mem_filter, mem_range]
    have := hd i
    omega
  simpa only [he, card_range, Nat.cast_id] using (sum_boole (R := ℕ) (fun x => x+1 ≤ d i) (range M))

noncomputable def jetMap {F I : Type*} [Field F] [Fintype I] {n : ℕ}
    (a : I → Fin n → F) (r : ℕ) : (I → F) →ₗ[F] (Jets n r → F) where
  toFun c m := ∑ l, c l * ∏ j, a l j ^ m.1 j
  map_add' x y := by funext m; simp [add_mul, sum_add_distrib]
  map_smul' x y := by funext m; simp [mul_sum, mul_assoc]

noncomputable def jetFlag {F I : Type*} [Field F] [Fintype I] {n : ℕ}
    (a : I → Fin n → F) : ℕ → Submodule F (I → F)
  | 0 => ⊤
  | r+1 => (jetMap a r).ker

lemma jetFlag_spec {F I : Type*} [Field F] [Fintype I] {n r : ℕ}
    (a : I → Fin n → F) (c : I → F) : c ∈ jetFlag a r ↔
      ∀ m : Fin n → ℕ, (∑ j, m j) < r → (∑ l, c l * ∏ j, a l j ^ m j) = 0 := by
  cases r with
  | zero => simp [jetFlag]
  | succ r =>
    change (jetMap a r) c = 0 ↔ _
    constructor
    · intro h m hm; exact congrFun h ⟨m, Nat.le_of_lt_succ hm⟩
    · intro h; funext m; exact h m.1 (Nat.lt_succ_of_le m.2)

lemma rank_jet {F I : Type*} [Field F] [Fintype I] {n : ℕ} (a : I → Fin n → F) (r : ℕ) :
    Fintype.card I ≤ Module.finrank F (jetFlag a (r+1)) + Fintype.card (Jets n r) := by
  let T := jetMap a r
  have h := T.finrank_range_add_finrank_ker
  have h' : Module.finrank F T.range ≤ Fintype.card (Jets n r) := by
    simpa using Submodule.finrank_le T.range
  simp only [Module.finrank_fintype_fun_eq_card] at h
  change _ ≤ Module.finrank F T.ker + _
  omega

lemma finite_obstruction {n p : ℕ} [Fact p.Prime] {I : Type*} [Fintype I] [LinearOrder I]
    (a : I → Fin n → ZMod p) (M : ℕ)
    (hsep : ∀ f : I → I, (∀ i, i ≤ f i) → (∀ j, ∑ i, a (f i) j = ∑ i, a i j) → f = id) :
    M * Fintype.card I ≤ (n+M).choose (n+1) + n*(p-1) := by
  classical
  obtain ⟨d, c, hd, hc, hr⟩ := depth_flags (jetFlag a) rfl M
  have hD := row_bound a c d (fun i => (jetFlag_spec a (c i)).mp (hc i).1)
    (fun i => (hc i).2.1) (fun i => (hc i).2.2) hsep
  rw [Fintype.card_fin] at hD
  have hsum := sum_le_sum (s := range M) (f := fun _ => Fintype.card I)
    (g := fun r => (univ.filter (fun i => r+1 ≤ d i)).card + (n+r).choose n) (fun r hr' => by
      have h := rank_jet a r
      rw [card_jets] at h
      exact h.trans (Nat.add_le_add_right (hr _ (Nat.succ_le_of_lt (mem_range.mp hr'))) _))
  rw [sum_add_distrib, sum_card_depth M d hd, hockey] at hsum
  simp only [sum_const, card_range, smul_eq_mul] at hsum
  omega

abbrev X (n : ℕ) := Fin n → ℝ
abbrev Z (n : ℕ) := Fin n → ℤ
def castZ {n : ℕ} (z : Z n) : X n := fun i => z i
@[simp] lemma castZ_zero (n : ℕ) : castZ (0 : Z n) = 0 := by funext i; simp [castZ]

lemma noWrap {n k p : ℕ} (_hk : 0 < k) {I : Type*} [Fintype I] [LinearOrder I]
    (a : I → Lex (Z n)) (ha : StrictMono a) (hI : 0 < Fintype.card I)
    {S : Set (X n)} (hc : Convex ℝ S) (hm : ∀ i, (k : ℝ)⁻¹ • castZ (ofLex (a i)) ∈ S)
    (hr : ∀ z : Z n, ((k : ℝ) * Fintype.card I)⁻¹ • (∑ i, castZ (ofLex (a i))) +
      ((p : ℝ) / ((k : ℝ) * Fintype.card I)) • castZ z ∈ S → z = 0)
    (f : I → I) (hf : ∀ i, i ≤ f i)
    (hmod : ∀ j, ∑ i, ((a (f i) j : ℤ) : ZMod p) = ∑ i, ((a i j : ℤ) : ZMod p)) : f = id := by
  classical
  have hdiv j : (p : ℤ) ∣ (∑ i, a (f i) j) - ∑ i, a i j := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    exact sub_eq_zero.mpr (hmod j)
  choose z hz using hdiv
  have heq : ((k : ℝ) * Fintype.card I)⁻¹ • (∑ i, castZ (ofLex (a i))) +
      ((p : ℝ) / ((k : ℝ) * Fintype.card I)) • castZ z =
      ((k : ℝ) * Fintype.card I)⁻¹ • (∑ i, castZ (ofLex (a (f i)))) := by
    funext j
    have hh := congrArg (fun x : ℤ => (x : ℝ)) (hz j)
    push_cast at hh
    change (∑ x, ((ofLex (a (f x)) j : ℤ) : ℝ)) - ∑ x, ((ofLex (a x) j : ℤ) : ℝ) = _ at hh
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, castZ]
    rw [div_eq_mul_inv, sub_eq_iff_eq_add.mp hh]
    ring
  have hsum : ((k : ℝ) * Fintype.card I)⁻¹ • (∑ i, castZ (ofLex (a (f i)))) ∈ S := by
    have hmean : ∑ i, ((Fintype.card I : ℝ)⁻¹) • ((k : ℝ)⁻¹ • castZ (ofLex (a (f i)))) ∈ S :=
      hc.sum_mem (fun _ _ => by positivity) (by simp [hI.ne']) (fun i _ => hm (f i))
    simp only [smul_smul, ← smul_sum] at hmean
    rwa [mul_comm, ← mul_inv] at hmean
  have hz0 := hr z (heq ▸ hsum)
  have hs : (∑ i, a (f i)) = ∑ i, a i := by
    change (∑ i, ofLex (a (f i)) : Z n) = ∑ i, ofLex (a i)
    funext j
    rw [Finset.sum_apply, Finset.sum_apply]
    have hh := hz j
    rw [hz0] at hh
    simpa [sub_eq_zero] using hh
  funext i
  apply le_antisymm ?_ (hf i)
  by_contra! hi
  exact (ne_of_lt (sum_lt_sum (fun j _ => ha.monotone (hf j)) ⟨i, mem_univ i, ha hi⟩)) hs.symm

end EhrhartAdapt
open Set
namespace EhrhartAdapt

noncomputable def sample {n : ℕ} (S : Set (X n)) (k : ℕ) : Set (X n) :=
  S ∩ (k : ℝ)⁻¹ • (↑(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) : Set (X n))
abbrev LatticeSample {n : ℕ} (S : Set (X n)) (k : ℕ) := {z : Lex (Z n) // (k : ℝ)⁻¹ • castZ (ofLex z) ∈ S}

noncomputable def sample_equiv {n k : ℕ} (hk : 0 < k) (S : Set (X n)) : LatticeSample S k ≃ sample S k := by
  classical
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  letI : NeZero k := ⟨hk.ne'⟩
  have hiff (x : X n) : x ∈ sample S k ↔ x ∈ S ∧ ∀ i, ∃ z : ℤ, (z : ℝ) = (k : ℝ) * x i := by
    rw [sample, mem_inter_iff, ← Submodule.coe_pointwise_smul]
    change x ∈ S ∧ x ∈ (k : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) ↔ _
    rw [BoxIntegral.unitPartition.mem_smul_span_iff (n := k)]
    rfl
  apply Equiv.ofBijective (fun z => (⟨(k : ℝ)⁻¹ • castZ (ofLex z.1), (hiff _).2 ⟨z.2, fun i => ⟨z.1 i, by
    change (z.1 i : ℝ) = (k : ℝ) * ((k : ℝ)⁻¹ * (z.1 i : ℝ))
    rw [← mul_assoc, mul_inv_cancel₀ hkr, one_mul]⟩⟩⟩ : sample S k))
  constructor
  · intro x y h
    apply Subtype.ext
    funext j
    have hh := congrFun (congrArg Subtype.val h) j
    change (k : ℝ)⁻¹ * (x.1 j : ℝ) = (k : ℝ)⁻¹ * (y.1 j : ℝ) at hh
    exact_mod_cast mul_left_cancel₀ (inv_ne_zero hkr) hh
  · intro x
    obtain ⟨hx, hm⟩ := (hiff _).mp x.2
    choose z hz using hm
    have h : (k : ℝ)⁻¹ • castZ z = x.1 := by
      funext i
      change (k : ℝ)⁻¹ * (z i : ℝ) = x.1 i
      rw [hz, ← mul_assoc, inv_mul_cancel₀ hkr, one_mul]
    exact ⟨⟨toLex z, h.symm ▸ hx⟩, Subtype.ext h⟩

lemma sample_finite {n k : ℕ} {S : Set (X n)} (hc : IsCompact S) (hk : 0 < k) : (sample S k).Finite := by
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold sample
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero hkr)]
  exact ZSpan.setFinite_inter _ hc.isBounded

noncomputable def num {n : ℕ} (S : Set (X n)) (k : ℕ) : ℕ := Nat.card (sample S k)
noncomputable def mean {n : ℕ} (S : Set (X n)) (k : ℕ) : X n :=
  fun i => (∑' x : sample S k, x.1 i) / (num S k : ℝ)

lemma num_pos {n k : ℕ} {S : Set (X n)} (hc : IsCompact S) (h0 : (0 : X n) ∈ S) (hk : 0 < k) : 0 < num S k := by
  let e := sample_equiv hk S
  let := (sample_finite hc hk).to_subtype
  let : Nonempty (sample S k) := ⟨e ⟨toLex 0, by simpa using h0⟩⟩
  exact Nat.card_pos

lemma mean_formula {n k : ℕ} {S : Set (X n)} (hk : 0 < k) [Fintype (LatticeSample S k)] :
    mean S k = ((k : ℝ) * Fintype.card (LatticeSample S k))⁻¹ •
      (∑ i : LatticeSample S k, castZ (ofLex i.1)) := by
  classical
  let e := sample_equiv hk S
  have hcard : num S k = Fintype.card (LatticeSample S k) := by
    rw [num, ← Nat.card_congr e, Nat.card_eq_fintype_card]
  funext j
  simp only [mean, hcard, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [← e.tsum_eq, tsum_fintype]
  have he (w : LatticeSample S k) : (e w).1 j = (k : ℝ)⁻¹ * castZ (ofLex w.1) j := rfl
  simp_rw [he]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_inv]
  ring

lemma count_limit {n : ℕ} {S : Set (X n)} (hc : Convex ℝ S) (hk : IsCompact S) :
    Tendsto (fun k : ℕ => (num S k : ℝ) / (k : ℝ)^n) atTop (𝓝 (volume.real S)) := by
  simpa [num, sample] using tendsto_card_div_pow_atTop_volume S hk.isBounded hk.measurableSet (hc.addHaar_frontier volume)

lemma mean_limit {n : ℕ} {S : Set (X n)} (hc : Convex ℝ S) (hk : IsCompact S)
    (h0 : (0 : X n) ∈ interior S) (hm : (∫ x in S, x ∂volume) = 0) :
    Tendsto (mean S) atTop (𝓝 0) := by
  have hV : 0 < volume.real S := ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume ⟨0,h0⟩).ne' hk.measure_ne_top
  apply tendsto_pi_nhds.mpr
  intro i
  let L : X n →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hi : (∫ x in S, x i ∂volume) = 0 := by
    calc
      _ = L (∫ x in S, x ∂volume) := L.integral_comp_comm (continuous_id.continuousOn.integrableOn_compact hk)
      _ = 0 := by rw [hm, map_zero]
  have ht : Tendsto (fun k : ℕ => (∑' x : sample S k, x.1 i) / (k : ℝ)^n) atTop (𝓝 0) := by
    simpa [sample, hi] using tendsto_tsum_div_pow_atTop_integral S (fun x => x i)
      (continuous_apply i) hk.isBounded hk.measurableSet (hc.addHaar_frontier volume)
  have h := ht.div (count_limit hc hk) hV.ne'
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk'
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  change (_ / (k : ℝ)^n) / (_ / (k : ℝ)^n) = mean S k i
  rw [div_div_div_cancel_right₀ (pow_ne_zero _ hkr)]
  rfl

lemma radial {n : ℕ} {S : Set (X n)} (hc : Convex ℝ S)
    (h0 : (0 : X n) ∈ interior S) (hl : ∀ z : Z n, castZ z ∈ interior S → z = 0)
    {ε : ℝ} (he : 0 < ε) : ∃ r : ℝ, 0 < r ∧
    ∀ b : X n, ‖b‖ < r → ∀ t : ℝ, 1 + ε ≤ t → ∀ z : Z n,
      b + t • castZ z ∈ S → z = 0 := by
  obtain ⟨δ, hd, hδ⟩ := Metric.isOpen_iff.mp isOpen_interior 0 h0
  refine ⟨ε * δ, mul_pos he hd, ?_⟩
  intro b hb t ht z hz
  have h1 : 1 < t := by linarith
  have htp : 0 < t := by linarith
  let q := -(t - 1)⁻¹ • b
  have hq : q ∈ interior S := by
    apply hδ
    simp only [Metric.mem_ball, dist_zero_right, q, norm_smul, norm_neg, Real.norm_eq_abs,
      abs_inv, abs_of_pos (sub_pos.mpr h1)]
    rw [← div_eq_inv_mul, div_lt_iff₀ (sub_pos.mpr h1)]
    nlinarith
  apply hl
  have hh : castZ z = t⁻¹ • (b + t • castZ z) + (1 - t⁻¹) • q := by
    have hh1 : t⁻¹ * t = 1 := inv_mul_cancel₀ htp.ne'
    have hh2 : (1 - t⁻¹) * -(t - 1)⁻¹ = -t⁻¹ := by
      field_simp [htp.ne', (sub_pos.mpr h1).ne']
    dsimp only [q]
    rw [smul_add, smul_smul, hh1, one_smul, smul_smul, hh2, neg_smul]
    abel
  rw [hh]
  exact hc.combo_closure_interior_mem_interior (subset_closure hz) hq (by positivity)
    (sub_pos.mpr (inv_lt_one_of_one_lt₀ h1)) (by ring)

lemma obstruction {n : ℕ} {S : Set (X n)} (hc : Convex ℝ S) (hk : IsCompact S)
    (h0 : (0 : X n) ∈ interior S) (hm : (∫ x in S, x ∂volume) = 0)
    (hl : ∀ z : Z n, castZ z ∈ interior S → z = 0) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ p : ℕ, p.Prime →
      (1+ε) * ((k : ℝ) * num S k) ≤ p → ((n+1)*k) * num S k ≤
        (n+((n+1)*k)).choose (n+1) + n*(p-1) := by
  classical
  obtain ⟨r, hp, hr⟩ := radial hc h0 hl he
  have hb := (mean_limit hc hk h0 hm).norm.eventually_lt_const (show ‖(0 : X n)‖ < r by simpa)
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with k hmean hk' p hprime hpr
  have hkpos : 0 < k := by omega
  let e := sample_equiv hkpos S
  let := (sample_finite hk hkpos).fintype
  let : Fintype (LatticeSample S k) := Fintype.ofEquiv (sample S k) e.symm
  let : Fact p.Prime := ⟨hprime⟩
  have hcard : num S k = Fintype.card (LatticeSample S k) := by
    rw [num, ← Nat.card_congr e, Nat.card_eq_fintype_card]
  have hi : 0 < Fintype.card (LatticeSample S k) := hcard ▸ num_pos hk (interior_subset h0) hkpos
  rw [hcard] at hpr ⊢
  refine finite_obstruction (fun (i : LatticeSample S k) j => (i.1 j : ZMod p)) ((n+1)*k) ?_
  apply noWrap hkpos Subtype.val (fun _ _ hab => hab) hi hc (fun i => i.2)
  rw [← mean_formula hkpos]
  apply hr _ hmean _
  exact (le_div_iff₀ (by positivity)).2 hpr

lemma cross (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (a b : ℝ) (ha : 0 < a)
    (hratio : ∀ᶠ k in atTop, a * s (k+1) ≤ b * s k) (N : ℕ) :
    ∃ k ≥ N, ∃ p : ℕ, p.Prime ∧ a * s k < p ∧ (p : ℝ) ≤ b * s k := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 hratio
  let L := max N M
  obtain ⟨m, hm⟩ := exists_nat_gt (a * s L)
  obtain ⟨p, hmp, hprime⟩ := Nat.exists_infinite_primes m
  have hpl : a * s L < p := hm.trans_le (by exact_mod_cast hmp)
  have hx : ∃ j : ℕ, (p : ℝ) ≤ a * s (L+j) := by
    obtain ⟨l, hl⟩ := eventually_atTop.1 (hs.eventually_ge_atTop ((p : ℝ) / a))
    exact ⟨l, by have h := hl (L+l) (by omega); rwa [div_le_iff₀ ha, mul_comm] at h⟩
  have hb := Nat.find_spec hx
  have hj : Nat.find hx ≠ 0 := by
    intro hz
    rw [hz, add_zero] at hb
    exact (not_le_of_gt hpl) hb
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hj
  have hlo := Nat.find_min hx (show j < Nat.find hx by omega)
  rw [hj] at hb
  refine ⟨L+j, by dsimp [L]; omega, p, hprime, lt_of_not_ge hlo, hb.trans ?_⟩
  exact hM (L+j) (by dsimp [L]; omega)

lemma analytic {n : ℕ} (S : Set (X n)) (hc : Convex ℝ S) (hk : IsCompact S)
    (h0 : (0 : X n) ∈ interior S) (hm : (∫ x in S, x ∂volume) = 0)
    (hl : ∀ z : Z n, castZ z ∈ interior S → z = 0) :
    volume.real S ≤ ((n : ℝ)+1)^n/n.factorial := by
  let V := volume.real S
  let A (k : ℕ) := (num S k : ℝ) / (k : ℝ)^n
  let s (k : ℕ) := (k : ℝ) * num S k
  have hV : 0 < V := ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume ⟨0,h0⟩).ne' hk.measure_ne_top
  have hA : Tendsto A atTop (𝓝 V) := count_limit hc hk
  have hs : Tendsto s atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k h
    have hp : (1 : ℝ) ≤ num S k := by exact_mod_cast num_pos hk (interior_subset h0) (show 0 < k by omega)
    dsimp [s]
    nlinarith
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsA (k : ℕ) (hk' : 0 < k) : s k / (k : ℝ)^(n+1) = A k := by
    have hr : (k : ℝ) ≠ 0 := by exact_mod_cast hk'.ne'
    dsimp [s,A]
    rw [pow_succ]
    field_simp
  have hshift : Tendsto (fun k : ℕ => s (k+1)/(k : ℝ)^(n+1)) atTop (𝓝 V) := by
    have hlim : Tendsto (fun k : ℕ => (1+(k : ℝ)⁻¹)^(n+1) * A (k+1)) atTop (𝓝 V) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hinv |>.pow (n+1)).mul (hA.comp (tendsto_add_atTop_nat 1))
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k h
    have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have heq : 1+(k : ℝ)⁻¹ = ((k+1 : ℕ) : ℝ) / (k : ℝ) := by push_cast; field_simp
    rw [heq, div_pow, ← hsA (k+1) (by omega), div_mul_div_comm]
    field_simp
  let C := ((n : ℝ)+1)^n/n.factorial
  let B (k : ℕ) := ((n : ℝ) * (k : ℝ)⁻¹ + ((n : ℝ)+1))^(n+1) / ((n+1).factorial : ℝ)
  have hB : Tendsto B atTop (𝓝 C) := by
    have h := ((((tendsto_const_nhds (x := (n : ℝ))).mul hinv).add (tendsto_const_nhds (x := (n : ℝ)+1))).pow (n+1)).div_const ((n+1).factorial : ℝ)
    have he : ((n : ℝ)+1)^(n+1) / ((n+1).factorial : ℝ) = C := by
      dsimp [C]
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    simpa [B, he] using h
  have hbnd (ε : ℝ) (he : 0 < ε) : (1-2*ε*(n : ℝ))*V ≤ C := by
    have hra : ∀ᶠ k in atTop, (1+ε)*s (k+1) ≤ (1+2*ε)*s k := by
      have h1 := (tendsto_const_nhds (x := 1+ε)).mul hshift
      have h2 := (tendsto_const_nhds (x := 1+2*ε)).mul hA
      filter_upwards [h1.eventually_lt h2 (by nlinarith : (1+ε)*V < (1+2*ε)*V), eventually_ge_atTop (1 : ℕ)] with k h hkn
      have hkp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      change (1+ε) * (s (k+1)/(k : ℝ)^(n+1)) < (1+2*ε) * A k at h
      rw [← hsA k (by omega), ← mul_div_assoc, ← mul_div_assoc] at h
      exact (div_lt_div_iff_of_pos_right (pow_pos hkp _)).mp h |>.le
    obtain ⟨N, hN⟩ := eventually_atTop.1 (obstruction hc hk h0 hm hl ε he)
    have hf : ∃ᶠ k in atTop, (1-2*ε*(n : ℝ))*A k - B k ≤ 0 := by
      rw [frequently_atTop]
      intro L
      obtain ⟨k, hkL, p, hprime, hpl, hpu⟩ := cross s hs (1+ε) (1+2*ε) (by linarith) hra (max 1 (max N L))
      have hk' : 0 < k := by omega
      have hkp : 0 < (k : ℝ) := by exact_mod_cast hk'
      have ho := hN k (by omega) p hprime hpl.le
      have hr : ((n : ℝ)+1) * s k ≤ ((n+((n+1)*k)).choose (n+1) : ℝ) + (n : ℝ) * p := by
        have hx : ((n+1)*k) * num S k ≤ (n+((n+1)*k)).choose (n+1) + n*p := ho.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _)
        simpa [s, mul_assoc] using (Nat.cast_le (α := ℝ)).mpr hx
      have hpc : (n : ℝ)*p ≤ (n : ℝ)*((1+2*ε)*s k) := mul_le_mul_of_nonneg_left hpu (by positivity)
      have hineq : (1-2*ε*(n : ℝ))*s k ≤ ((n+((n+1)*k)).choose (n+1) : ℝ) := by linarith
      have hcb : ((n+((n+1)*k)).choose (n+1) : ℝ) / (k : ℝ)^(n+1) ≤ B k := by
        have hv := Nat.descFactorial_le_pow (n+((n+1)*k)) (n+1)
        rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm] at hv
        have hh : ((n+((n+1)*k)).choose (n+1) : ℝ) * ((n+1).factorial : ℝ) ≤ (((n+((n+1)*k) : ℕ) : ℝ)^(n+1)) := by exact_mod_cast hv
        have hg : ((n : ℝ) * (k : ℝ)⁻¹ + ((n : ℝ)+1)) = ((n+((n+1)*k) : ℕ) : ℝ)/(k : ℝ) := by
          push_cast
          field_simp
        dsimp [B]
        rw [hg, div_pow, div_right_comm]
        exact div_le_div_of_nonneg_right ((le_div_iff₀ (by positivity)).2 hh) (by positivity)
      refine ⟨k, by omega, sub_nonpos.mpr ?_⟩
      rw [← hsA k hk', ← mul_div_assoc]
      exact (div_le_div_of_nonneg_right hineq (by positivity)).trans hcb
    exact sub_nonpos.mp (le_of_tendsto_of_frequently (((tendsto_const_nhds (x := 1-2*ε*(n : ℝ))).mul hA).sub hB) hf)
  have hlim : Tendsto (fun ε : ℝ => (1-2*ε*(n : ℝ))*V) (𝓝[>] 0) (𝓝 V) := by
    have h := (show Continuous (fun ε : ℝ => (1-2*ε*(n : ℝ))*V) by fun_prop).continuousWithinAt (s := Ioi 0) (x := 0)
    simpa [ContinuousWithinAt] using h
  exact le_of_tendsto hlim (mem_of_superset self_mem_nhdsWithin (fun ε he => hbnd ε he))

open OMA.S_wp_ehrhart_s_volume_conjecture
lemma reduce {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hlat : interior K ∩ integerLattice n = {c}) (hcent : centerOfMass K = c) :
    ∃ S : Set (X n), Convex ℝ S ∧ IsCompact S ∧ (0 : X n) ∈ interior S ∧
      (∀ z : Z n, castZ z ∈ interior S → z = 0) ∧
      (∫ x in S, x ∂volume) = 0 ∧ volume S = volume K := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let e := L.toHomeomorph.trans (Homeomorph.addRight (- L c))
  have he (x : EuclideanSpace ℝ (Fin n)) : e x = L x + -L c := rfl
  have hec : e c = 0 := by rw [he, add_neg_cancel]
  have hm : MeasurePreserving e volume volume :=
    (PiLp.volume_preserving_ofLp (Fin n)).add_right volume (-L c)
  have hc : c ∈ interior K ∩ integerLattice n := hlat.symm ▸ mem_singleton c
  have hmes : volume (e '' K) = volume K := by
    have h := hm.measure_preimage (hcomp.image e.continuous).measurableSet.nullMeasurableSet
    rw [preimage_image_eq _ e.injective] at h
    exact h.symm
  refine ⟨e '' K, ?_, hcomp.image e.continuous, ?_, ?_, ?_, hmes⟩
  · have h : e '' K = (fun y => -L c + y) '' (L.toLinearEquiv.toLinearMap '' K) := by
      rw [image_image]
      congr 1
      funext x
      rw [he, add_comm]
      rfl
    rw [h]
    exact (hconv.linear_image L.toLinearEquiv.toLinearMap).translate (-L c)
  · rw [← e.image_interior]
    exact ⟨c, hc.1, hec⟩
  · intro z hz
    rw [← e.image_interior] at hz
    obtain ⟨x, hx, hxe⟩ := hz
    have hxl : x ∈ integerLattice n := by
      intro i
      obtain ⟨a, ha⟩ := hc.2 i
      refine ⟨z i + a, ?_⟩
      rw [he] at hxe
      have hh := congrFun hxe i
      change x i + -c i = (z i : ℝ) at hh
      push_cast
      linarith
    have hxc : x = c := by simpa [hlat] using (show x ∈ interior K ∩ integerLattice n from ⟨hx, hxl⟩)
    rw [hxc, hec] at hxe
    funext i
    have hh : (z i : ℝ) = 0 := congrFun hxe.symm i
    change z i = 0
    exact_mod_cast hh
  · rw [hm.setIntegral_image_emb e.toMeasurableEquiv.measurableEmbedding]
    simp_rw [he]
    have hid : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => x) K volume :=
      continuous_id.continuousOn.integrableOn_compact hcomp
    have hlin : IntegrableOn (fun x => L x) K volume :=
      L.continuous.continuousOn.integrableOn_compact hcomp
    have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => -L c) K volume :=
      integrableOn_const hcomp.measure_ne_top
    rw [integral_add hlin hconst, setIntegral_const]
    have hi : (∫ x in K, L x ∂volume) = L (∫ x in K, x ∂volume) :=
      L.toContinuousLinearMap.integral_comp_comm hid
    rw [hi]
    have hv : (volume K).toReal ≠ 0 := (ENNReal.toReal_pos
      (Measure.measure_pos_of_nonempty_interior volume ⟨c, hc.1⟩).ne' hcomp.measure_ne_top).ne'
    have hmul := congrArg (fun x => (volume K).toReal • x) hcent
    change (volume K).toReal • ((volume K).toReal⁻¹ • (∫ x in K, x ∂volume)) = _ at hmul
    rw [smul_smul, mul_inv_cancel₀ hv, one_smul] at hmul
    rw [hmul, map_smul, smul_neg, Measure.real, add_neg_cancel]
end EhrhartAdapt

theorem OMA.solution : type_of% @OMA.S_wp_ehrhart_s_volume_conjecture.main := by
  intro n K c hconv hcomp hint hlat hcent
  obtain ⟨S, hc, hk, h0, hl, hm, hvol⟩ := EhrhartAdapt.reduce K c hconv hcomp hlat hcent
  rw [← hvol, ← ENNReal.ofReal_toReal hk.measure_ne_top]
  exact ENNReal.ofReal_le_ofReal (EhrhartAdapt.analytic S hc hk h0 hm hl)
