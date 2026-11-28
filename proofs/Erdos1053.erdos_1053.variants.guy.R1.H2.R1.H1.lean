import OMAReductions.R_Erdos1053_erdos_1053_variants_guy_R1_H2_R1

/-!
Proof of `Erdos1053.erdos_1053.variants.guy.R1.H2.R1.H1` (Dickson 1913 / odd-parity argument):
for every `r` and `k ≥ 1`, there are only finitely many odd `n` with `σ 1 n = k * n` and
`n.primeFactors.card ≤ r`.

Assuming infinitely many such `n`, pass to a fixed number `s` of distinct prime factors and
extract a subsequence along which every prime coordinate `P m i` and exponent coordinate `E m i`
is either constant or strictly increasing. Partition `Fin s` into `C` (both constant), `I`
(constant prime, strictly increasing exponent), and `U` (strictly increasing prime), with
`I ∪ U ≠ ∅`. Passing to the limit of `σ 1 (f m) / f m = k` gives
`k = (∏ i ∈ C, σ(p_i^{e_i}) / p_i^{e_i}) * (∏ i ∈ I, p_i / (p_i - 1))`.
Substituting `m = 0`, cancelling the positive common factor, and clearing denominators yields
`(∏ i ∈ I, (p_i^{e_{0,i}+1} - 1)) * (∏ i ∈ U, σ(p_{0,i}^{e_{0,i}})) = (∏ i ∈ I, p_i^{e_{0,i}+1}) * (∏ i ∈ U, p_{0,i}^{e_{0,i}})`.
If `I = ∅` then `U ≠ ∅` makes LHS strictly larger than RHS; if `I ≠ ∅` then every prime dividing
odd `f 0` is odd, making LHS even and RHS odd. Contradiction.
-/

namespace OMA.Erdos1053H1

/-- Elementary ε-N convergence on `ℕ → ℝ`. -/
private def ConvergesTo (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → |f m - a| < ε

private lemma convergesTo_const (a : ℝ) : ConvergesTo (fun _ => a) a :=
  fun ε hε => ⟨0, fun _ _ => by simpa using hε⟩

private lemma convergesTo_unique {f : ℕ → ℝ} {a b : ℝ}
    (ha : ConvergesTo f a) (hb : ConvergesTo f b) : a = b := by
  by_contra hne
  have hpos : 0 < |a - b| / 2 := by
    have : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
    linarith
  obtain ⟨N₁, hN₁⟩ := ha (|a - b| / 2) hpos
  obtain ⟨N₂, hN₂⟩ := hb (|a - b| / 2) hpos
  let m := max N₁ N₂
  have h1 : |f m - a| < |a - b| / 2 := hN₁ m (le_max_left _ _)
  have h2 : |f m - b| < |a - b| / 2 := hN₂ m (le_max_right _ _)
  have htri : |a - b| ≤ |a - f m| + |f m - b| := abs_sub_le a (f m) b
  rw [abs_sub_comm a (f m)] at htri
  linarith

private lemma convergesTo_mul {f g : ℕ → ℝ} {a b : ℝ}
    (hf : ConvergesTo f a) (hg : ConvergesTo g b) :
    ConvergesTo (fun m => f m * g m) (a * b) := by
  intro ε hε
  have hbp : 0 < |b| + 1 := by positivity
  have hap : 0 < |a| + 1 := by positivity
  obtain ⟨N₀, hN₀⟩ := hg 1 zero_lt_one
  obtain ⟨N₁, hN₁⟩ := hf (ε / (2 * (|b| + 1))) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hg (ε / (2 * (|a| + 1))) (by positivity)
  refine ⟨max N₀ (max N₁ N₂), fun m hm => ?_⟩
  have h0 : |g m - b| < 1 := hN₀ m (le_trans (le_max_left _ _) hm)
  have h1 : |f m - a| < ε / (2 * (|b| + 1)) :=
    hN₁ m (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm)
  have h2 : |g m - b| < ε / (2 * (|a| + 1)) :=
    hN₂ m (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm)
  have hgm : |g m| ≤ |b| + 1 := by
    have htri : |g m| ≤ |g m - b| + |b| := by
      simpa [sub_add_cancel] using abs_add_le (g m - b) b
    linarith
  have hsplit : f m * g m - a * b = (f m - a) * g m + a * (g m - b) := by ring
  have hle1 : |f m * g m - a * b| ≤ |f m - a| * |g m| + |a| * |g m - b| := by
    rw [hsplit]
    simpa [abs_mul] using abs_add_le ((f m - a) * g m) (a * (g m - b))
  have ht1 : |f m - a| * |g m| < ε / 2 := by
    calc |f m - a| * |g m|
        ≤ |f m - a| * (|b| + 1) := mul_le_mul_of_nonneg_left hgm (abs_nonneg _)
      _ < (ε / (2 * (|b| + 1))) * (|b| + 1) := mul_lt_mul_of_pos_right h1 hbp
      _ = ε / 2 := by field_simp
  have ht2 : |a| * |g m - b| < ε / 2 := by
    calc |a| * |g m - b|
        ≤ (|a| + 1) * |g m - b| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (|a| + 1) * (ε / (2 * (|a| + 1))) := mul_lt_mul_of_pos_left h2 hap
      _ = ε / 2 := by field_simp
  linarith

private lemma convergesTo_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ → ℝ) (a : ι → ℝ) (h : ∀ i ∈ s, ConvergesTo (f i) (a i)) :
    ConvergesTo (fun m => ∏ i ∈ s, f i m) (∏ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using convergesTo_const (1 : ℝ)
  | insert x s hx ih =>
    have hx' : ConvergesTo (f x) (a x) := h x (Finset.mem_insert_self x s)
    have hs' : ConvergesTo (fun m => ∏ i ∈ s, f i m) (∏ i ∈ s, a i) :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.prod_insert hx] using convergesTo_mul hx' hs'

private lemma strictMono_id_le {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hf (Nat.lt_succ_self n)))

private lemma exists_gt_of_infinite {A : Set ℕ} (hA : A.Infinite) (m : ℕ) :
    ∃ k ∈ A, m < k := by
  by_contra h
  push Not at h
  have hsub : A ⊆ ((Finset.range (m + 1) : Finset ℕ) : Set ℕ) := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_range]
    have := h x hx
    omega
  exact hA ((Finset.range (m + 1)).finite_toSet.subset hsub)

private lemma strictMono_of_infinite {A : Set ℕ} (hA : A.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, φ n ∈ A := by
  have hex : ∀ m : ℕ, ∃ k, m < k ∧ k ∈ A := fun m => by
    obtain ⟨k, hkA, hkm⟩ := exists_gt_of_infinite hA m
    exact ⟨k, hkm, hkA⟩
  classical
  let φ : ℕ → ℕ := Nat.rec (Classical.choose (hex 0)) (fun _ prev => Classical.choose (hex prev))
  refine ⟨φ, strictMono_nat_of_lt_succ (fun n => (Classical.choose_spec (hex (φ n))).1), fun n => ?_⟩
  cases n with
  | zero => exact (Classical.choose_spec (hex 0)).2
  | succ n => exact (Classical.choose_spec (hex (φ n))).2

private lemma exists_const_or_strictMono (g : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ((∃ c, ∀ n, g (φ n) = c) ∨ StrictMono (g ∘ φ)) := by
  by_cases hfin : (Set.range g).Finite
  · have hfib : ∃ c ∈ Set.range g, ({n : ℕ | g n = c}).Infinite := by
      by_contra hall
      push Not at hall
      have huniv : (Set.univ : Set ℕ) ⊆ ⋃ c ∈ Set.range g, {n : ℕ | g n = c} := by
        intro n _
        exact Set.mem_biUnion ⟨n, rfl⟩ rfl
      have hfin_u : (Set.univ : Set ℕ).Finite :=
        (hfin.biUnion fun c hc => hall c hc).subset huniv
      exact Set.infinite_univ hfin_u
    obtain ⟨c, _, hinf⟩ := hfib
    obtain ⟨φ, hφ, hmem⟩ := strictMono_of_infinite hinf
    exact ⟨φ, hφ, Or.inl ⟨c, hmem⟩⟩
  · have hinf : (Set.range g).Infinite := hfin
    have hex : ∀ m : ℕ, ∃ k, m < k ∧ g m < g k := fun m => by
      let M := (Finset.range (m + 1)).sup g
      obtain ⟨y, ⟨k, rfl⟩, hMy⟩ := exists_gt_of_infinite hinf M
      have hmk : m < k := by
        by_contra hle
        have hmem : k ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
        have hleM : g k ≤ M := Finset.le_sup (f := g) hmem
        omega
      have hgm : g m ≤ M :=
        Finset.le_sup (f := g) (Finset.mem_range.mpr (Nat.lt_succ_self m))
      exact ⟨k, hmk, lt_of_le_of_lt hgm hMy⟩
    classical
    let φ : ℕ → ℕ := Nat.rec 0 (fun _ prev => Classical.choose (hex prev))
    refine ⟨φ, strictMono_nat_of_lt_succ (fun n => (Classical.choose_spec (hex (φ n))).1),
      Or.inr (strictMono_nat_of_lt_succ (fun n => (Classical.choose_spec (hex (φ n))).2))⟩

private lemma extract_subseq {s : ℕ} (P E : ℕ → Fin s → ℕ) :
    ∀ k ≤ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : Fin s, i.1 < k →
        ((∃ c, ∀ m, P (φ m) i = c) ∨ StrictMono (fun m => P (φ m) i)) ∧
        ((∃ c, ∀ m, E (φ m) i = c) ∨ StrictMono (fun m => E (φ m) i)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨id, strictMono_id, fun i hi => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨φ₁, hφ₁, hprev⟩ := ih (by omega)
    let idx : Fin s := ⟨k, hk⟩
    obtain ⟨φ₂, hφ₂, hP₂⟩ := exists_const_or_strictMono (fun m => P (φ₁ m) idx)
    obtain ⟨φ₃, hφ₃, hE₃⟩ := exists_const_or_strictMono (fun m => E (φ₁ (φ₂ m)) idx)
    refine ⟨fun m => φ₁ (φ₂ (φ₃ m)), hφ₁.comp (hφ₂.comp hφ₃), fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · obtain ⟨hPi, hEi⟩ := hprev i hlt
      constructor
      · rcases hPi with ⟨c, hc⟩ | hsm
        · exact Or.inl ⟨c, fun m => hc (φ₂ (φ₃ m))⟩
        · exact Or.inr (hsm.comp (hφ₂.comp hφ₃))
      · rcases hEi with ⟨c, hc⟩ | hsm
        · exact Or.inl ⟨c, fun m => hc (φ₂ (φ₃ m))⟩
        · exact Or.inr (hsm.comp (hφ₂.comp hφ₃))
    · have hidx : i = idx := Fin.ext heq
      subst hidx
      constructor
      · rcases hP₂ with ⟨c, hc⟩ | hsm
        · exact Or.inl ⟨c, fun m => hc (φ₃ m)⟩
        · exact Or.inr (hsm.comp hφ₃)
      · exact hE₃

private lemma geom_sum_real (x : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, x ^ j) * (x - 1) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

private noncomputable def ratio (p e : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 (p ^ e) : ℝ) / ((p ^ e : ℕ) : ℝ)

private lemma sigma_prime_pow_ge {p e : ℕ} (hp : p.Prime) :
    p ^ e ≤ ArithmeticFunction.sigma 1 (p ^ e) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  exact Finset.single_le_sum (f := fun j => p ^ j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_self e))

private lemma pow_lt_sigma_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    p ^ e < ArithmeticFunction.sigma 1 (p ^ e) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le' he
  rw [Finset.sum_range_succ', pow_zero]
  have hle : p ^ (e' + 1) ≤ ∑ k ∈ Finset.range (e' + 1), p ^ (k + 1) :=
    Finset.single_le_sum (f := fun k => p ^ (k + 1)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_self e'))
  omega

private lemma ratio_eq {p e : ℕ} (hp : p.Prime) :
    ratio p e = ((p : ℝ) / ((p : ℝ) - 1)) * (1 - 1 / ((p : ℝ) ^ (e + 1))) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hsum : (ArithmeticFunction.sigma 1 (p ^ e) : ℝ) * ((p : ℝ) - 1) = (p : ℝ) ^ (e + 1) - 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    push_cast
    exact geom_sum_real (p : ℝ) (e + 1)
  have h1 : (ArithmeticFunction.sigma 1 (p ^ e) : ℝ) = ((p : ℝ) ^ (e + 1) - 1) / ((p : ℝ) - 1) :=
    eq_div_of_mul_eq hp1 hsum
  have hpow : ((p ^ e : ℕ) : ℝ) = (p : ℝ) ^ e := by push_cast; rfl
  dsimp only [ratio]
  rw [h1, hpow]
  field_simp
  rw [pow_succ]
  ring

private lemma ratio_ge_one {p e : ℕ} (hp : p.Prime) : (1 : ℝ) ≤ ratio p e := by
  dsimp only [ratio]
  have hpos : (0 : ℝ) < ((p ^ e : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos e
  rw [one_le_div hpos]
  exact_mod_cast sigma_prime_pow_ge hp

private lemma ratio_le_bound {p e : ℕ} (hp : p.Prime) :
    ratio p e ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  rw [ratio_eq hp]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hfrac : (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (by linarith) (by linarith)
  have hinv : (0 : ℝ) ≤ 1 / ((p : ℝ) ^ (e + 1)) := by positivity
  nlinarith

private lemma convergesTo_ratio_exp {p : ℕ} (hp : p.Prime) {e : ℕ → ℕ} (he : StrictMono e) :
    ConvergesTo (fun m => ratio p (e m)) ((p : ℝ) / ((p : ℝ) - 1)) := by
  intro ε hε
  refine ⟨⌈2 / ε⌉₊ + 1, fun m hm => ?_⟩
  dsimp only
  rw [ratio_eq hp]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hfrac_pos : (0 : ℝ) < (p : ℝ) / ((p : ℝ) - 1) := div_pos (by linarith) (by linarith)
  have hfrac_le : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
    linarith
  have hdiff : ((p : ℝ) / ((p : ℝ) - 1)) * (1 - 1 / ((p : ℝ) ^ (e m + 1))) -
      (p : ℝ) / ((p : ℝ) - 1) = -(((p : ℝ) / ((p : ℝ) - 1)) / ((p : ℝ) ^ (e m + 1))) := by ring
  rw [hdiff, abs_neg, abs_of_nonneg (by positivity)]
  have hm_le : m + 1 ≤ p ^ (e m + 1) := by
    have h1 : m ≤ e m := strictMono_id_le he m
    have h2 : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ (m + 1) ≤ p ^ (e m + 1) :=
      (Nat.pow_le_pow_left hp.two_le (m + 1)).trans (Nat.pow_le_pow_right hp.pos (by omega))
    omega
  have hm_real : ((m : ℝ) + 1) ≤ (p : ℝ) ^ (e m + 1) := by exact_mod_cast hm_le
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hceil : 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
  have hm_gt : 2 / ε < (m : ℝ) + 1 := by
    have : (⌈2 / ε⌉₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  calc ((p : ℝ) / ((p : ℝ) - 1)) / ((p : ℝ) ^ (e m + 1))
      ≤ 2 / ((p : ℝ) ^ (e m + 1)) := div_le_div_of_nonneg_right hfrac_le (by positivity)
    _ ≤ 2 / ((m : ℝ) + 1) := div_le_div_of_nonneg_left (by norm_num) hm_pos hm_real
    _ < ε := by
        rw [div_lt_iff₀ hm_pos]
        have := (div_lt_iff₀ hε).mp hm_gt
        linarith

private lemma convergesTo_ratio_prime {p e : ℕ → ℕ}
    (hp : ∀ m, (p m).Prime) (hsm : StrictMono p) :
    ConvergesTo (fun m => ratio (p m) (e m)) 1 := by
  intro ε hε
  refine ⟨⌈1 / ε⌉₊ + 2, fun m hm => ?_⟩
  have hge1 : (1 : ℝ) ≤ ratio (p m) (e m) := ratio_ge_one (hp m)
  have hle : ratio (p m) (e m) ≤ (p m : ℝ) / ((p m : ℝ) - 1) := ratio_le_bound (hp m)
  rw [abs_of_nonneg (by linarith)]
  have hpm_ge : (m : ℝ) ≤ (p m : ℝ) := by exact_mod_cast strictMono_id_le hsm m
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by
    have : 2 ≤ m := by omega
    exact_mod_cast this
  have hceil : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
  have hm_sub : 1 / ε < (m : ℝ) - 1 := by
    have : (⌈1 / ε⌉₊ : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hpm1 : (0 : ℝ) < (p m : ℝ) - 1 := by linarith
  have hsub_eq : (p m : ℝ) / ((p m : ℝ) - 1) - 1 = 1 / ((p m : ℝ) - 1) := by
    field_simp; ring
  calc ratio (p m) (e m) - 1
      ≤ (p m : ℝ) / ((p m : ℝ) - 1) - 1 := by linarith
    _ = 1 / ((p m : ℝ) - 1) := hsub_eq
    _ ≤ 1 / ((m : ℝ) - 1) := div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)
    _ < ε := by
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (m : ℝ) - 1)]
        have := (div_lt_iff₀ hε).mp hm_sub
        linarith

private lemma odd_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℕ)
    (h : ∀ i ∈ s, Odd (g i)) : Odd (∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using odd_one
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    exact (h x (Finset.mem_insert_self x s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma finite_odd_perfect_fixed_card (s k : ℕ) (hk : 1 ≤ k) :
    {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Odd n ∧ n.primeFactors.card = s}.Finite := by
  classical
  by_contra hinf
  have hinf' : {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Odd n ∧ n.primeFactors.card = s}.Infinite := hinf
  obtain ⟨f₀, hf₀_sm, hf₀_mem⟩ := strictMono_of_infinite hinf'
  let ord₀ : ∀ m, Fin s ≃o (f₀ m).primeFactors :=
    fun m => (f₀ m).primeFactors.orderIsoOfFin (hf₀_mem m).2.2
  let P₀ : ℕ → Fin s → ℕ := fun m i => (ord₀ m i).1
  let E₀ : ℕ → Fin s → ℕ := fun m i => (f₀ m).factorization (P₀ m i)
  obtain ⟨φ, hφ_sm, hcoord⟩ := extract_subseq P₀ E₀ s le_rfl
  let f : ℕ → ℕ := fun m => f₀ (φ m)
  let P : ℕ → Fin s → ℕ := fun m i => P₀ (φ m) i
  let E : ℕ → Fin s → ℕ := fun m i => E₀ (φ m) i
  have hf_sm : StrictMono f := hf₀_sm.comp hφ_sm
  have hf_perf : ∀ m, Nat.IsPerfectFor (f m) 1 k := fun m => (hf₀_mem (φ m)).1
  have hf_odd : ∀ m, Odd (f m) := fun m => (hf₀_mem (φ m)).2.1
  have hf_pos : ∀ m, 0 < f m := fun m => (hf_perf m).1
  have hf_sig : ∀ m, ArithmeticFunction.sigma 1 (f m) = k * f m := fun m => by
    simpa [Nat.IsPerfectFor] using (hf_perf m).2
  have hP_mem : ∀ m i, P m i ∈ (f m).primeFactors := fun m i => (ord₀ (φ m) i).2
  have hP_prime : ∀ m i, (P m i).Prime := fun m i => Nat.prime_of_mem_primeFactors (hP_mem m i)
  have hE_pos : ∀ m i, 1 ≤ E m i := fun m i => by
    have hmem : P m i ∈ (f m).factorization.support := hP_mem m i
    have hne : (f m).factorization (P m i) ≠ 0 := Finsupp.mem_support_iff.mp hmem
    exact Nat.pos_of_ne_zero hne
  have hprod_bij : ∀ m (g : ℕ → ℕ),
      ∏ p ∈ (f m).primeFactors, g p = ∏ i : Fin s, g (P m i) := by
    intro m g
    symm
    refine Finset.prod_bij (fun (i : Fin s) _ => P m i)
      (fun i _ => hP_mem m i)
      (fun i₁ _ i₂ _ h => (ord₀ (φ m)).injective (Subtype.ext h))
      (fun p hp => ⟨(ord₀ (φ m)).symm ⟨p, hp⟩, Finset.mem_univ _, by simp [P, P₀]⟩)
      (fun _ _ => rfl)
  have hf_eq_prod : ∀ m, f m = ∏ i : Fin s, P m i ^ E m i := fun m => by
    change f m = ∏ i : Fin s, P m i ^ (f m).factorization (P m i)
    rw [← hprod_bij m (fun p => p ^ (f m).factorization p)]
    exact Nat.prod_primeFactors_pow_factorization (hf_pos m).ne'
  have hsig_eq_prod : ∀ m, ArithmeticFunction.sigma 1 (f m) =
      ∏ i : Fin s, ArithmeticFunction.sigma 1 (P m i ^ E m i) := fun m => by
    change ArithmeticFunction.sigma 1 (f m) =
      ∏ i : Fin s, ArithmeticFunction.sigma 1 (P m i ^ (f m).factorization (P m i))
    rw [← hprod_bij m (fun p => ArithmeticFunction.sigma 1 (p ^ (f m).factorization p))]
    have hpair : ((f m).primeFactors : Set ℕ).Pairwise
        (Function.onFun Nat.Coprime (fun p => p ^ (f m).factorization p)) := by
      intro p hp q hq hpq
      exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq).pow _ _
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (hf_pos m).ne']
    exact ArithmeticFunction.isMultiplicative_sigma.map_prod _ _ hpair
  have hratio_prod : ∀ m, ∏ i : Fin s, ratio (P m i) (E m i) = (k : ℝ) := fun m => by
    dsimp only [ratio]
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
        ← hsig_eq_prod m, ← hf_eq_prod m, hf_sig m, Nat.cast_mul]
    have hne : (f m : ℝ) ≠ 0 := by exact_mod_cast (hf_pos m).ne'
    exact mul_div_cancel_right₀ (k : ℝ) hne
  let U : Finset (Fin s) := Finset.univ.filter (fun i => StrictMono (fun m => P m i))
  let I : Finset (Fin s) := Finset.univ.filter
    (fun i => ¬ StrictMono (fun m => P m i) ∧ StrictMono (fun m => E m i))
  let C : Finset (Fin s) := Finset.univ.filter
    (fun i => ¬ StrictMono (fun m => P m i) ∧ ¬ StrictMono (fun m => E m i))
  have hP_const_of_not_U : ∀ i, ¬ StrictMono (fun m => P m i) → ∀ m, P m i = P 0 i := by
    intro i hnu m
    rcases (hcoord i i.2).1 with ⟨c, hc⟩ | hsm
    · exact (hc m).trans (hc 0).symm
    · exact (hnu hsm).elim
  have hE_const_of_C : ∀ i ∈ C, ∀ m, E m i = E 0 i := by
    intro i hi m
    have hne : ¬ StrictMono (fun m => E m i) := (Finset.mem_filter.mp hi).2.2
    rcases (hcoord i i.2).2 with ⟨c, hc⟩ | hsm
    · exact (hc m).trans (hc 0).symm
    · exact (hne hsm).elim
  have hP_const_C : ∀ i ∈ C, ∀ m, P m i = P 0 i := fun i hi =>
    hP_const_of_not_U i (Finset.mem_filter.mp hi).2.1
  have hP_const_I : ∀ i ∈ I, ∀ m, P m i = P 0 i := fun i hi =>
    hP_const_of_not_U i (Finset.mem_filter.mp hi).2.1
  have hE_sm_I : ∀ i ∈ I, StrictMono (fun m => E m i) := fun i hi =>
    (Finset.mem_filter.mp hi).2.2
  have hP_sm_U : ∀ i ∈ U, StrictMono (fun m => P m i) := fun i hi =>
    (Finset.mem_filter.mp hi).2
  have hsplit : ∀ (g : Fin s → ℝ),
      ∏ i : Fin s, g i = (∏ i ∈ C, g i) * (∏ i ∈ I, g i) * (∏ i ∈ U, g i) := by
    intro g
    have h1 := (Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i : Fin s => StrictMono (fun m => P m i)) g).symm
    have h2 := (Finset.prod_filter_mul_prod_filter_not
      (Finset.univ.filter (fun i : Fin s => ¬ StrictMono (fun m => P m i)))
      (fun i : Fin s => StrictMono (fun m => E m i)) g).symm
    have hI_eq : (Finset.univ.filter (fun i : Fin s => ¬ StrictMono (fun m => P m i))).filter
        (fun i => StrictMono (fun m => E m i)) = I := by
      ext i; simp [I]
    have hC_eq : (Finset.univ.filter (fun i : Fin s => ¬ StrictMono (fun m => P m i))).filter
        (fun i => ¬ StrictMono (fun m => E m i)) = C := by
      ext i; simp [C]
    rw [hI_eq, hC_eq] at h2
    rw [h1, h2]
    ring
  have hIU_nonempty : I.Nonempty ∨ U.Nonempty := by
    by_contra h
    push Not at h
    obtain ⟨hIe, hUe⟩ := h
    have hC_all : ∀ i : Fin s, i ∈ C := fun i => by
      have hiU : i ∉ U := by simp [hUe]
      have hiI : i ∉ I := by simp [hIe]
      simp only [U, I, C, Finset.mem_filter, Finset.mem_univ, true_and] at hiU hiI ⊢
      exact ⟨hiU, fun hE => hiI ⟨hiU, hE⟩⟩
    have hf01 : f 0 = f 1 := by
      rw [hf_eq_prod 0, hf_eq_prod 1]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hP_const_C i (hC_all i) 1, hE_const_of_C i (hC_all i) 1]
    have hlt : f 0 < f 1 := hf_sm (by decide : 0 < 1)
    omega
  -- Take limits of each coordinate
  let L : Fin s → ℝ := fun i =>
    if i ∈ U then 1
    else if i ∈ I then (P 0 i : ℝ) / ((P 0 i : ℝ) - 1)
    else ratio (P 0 i) (E 0 i)
  have hconv_coord : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      ConvergesTo (fun m => ratio (P m i) (E m i)) (L i) := by
    intro i _
    by_cases hiU : i ∈ U
    · simp only [L, if_pos hiU]
      exact convergesTo_ratio_prime (fun m => hP_prime m i) (hP_sm_U i hiU)
    · by_cases hiI : i ∈ I
      · simp only [L, if_neg hiU, if_pos hiI]
        have hcongr : (fun m => ratio (P m i) (E m i)) = (fun m => ratio (P 0 i) (E m i)) := by
          funext m; rw [hP_const_I i hiI m]
        rw [hcongr]
        exact convergesTo_ratio_exp (hP_prime 0 i) (hE_sm_I i hiI)
      · have hiC : i ∈ C := by
          simp only [U, I, C, Finset.mem_filter, Finset.mem_univ, true_and] at hiU hiI ⊢
          exact ⟨hiU, fun hE => hiI ⟨hiU, hE⟩⟩
        simp only [L, if_neg hiU, if_neg hiI]
        have hcongr : (fun m => ratio (P m i) (E m i)) = (fun _ => ratio (P 0 i) (E 0 i)) := by
          funext m; rw [hP_const_C i hiC m, hE_const_of_C i hiC m]
        rw [hcongr]
        exact convergesTo_const _
  have hconv_prod : ConvergesTo (fun m => ∏ i : Fin s, ratio (P m i) (E m i))
      (∏ i : Fin s, L i) :=
    convergesTo_finset_prod Finset.univ (fun i m => ratio (P m i) (E m i)) L hconv_coord
  have hconv_k : ConvergesTo (fun m => ∏ i : Fin s, ratio (P m i) (E m i)) (k : ℝ) := by
    have : (fun m => ∏ i : Fin s, ratio (P m i) (E m i)) = fun _ => (k : ℝ) := by
      funext m; exact hratio_prod m
    rw [this]
    exact convergesTo_const (k : ℝ)
  have hk_eq_L : (k : ℝ) = ∏ i : Fin s, L i := convergesTo_unique hconv_k hconv_prod
  have hL_C : ∏ i ∈ C, L i = ∏ i ∈ C, ratio (P 0 i) (E 0 i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hiU : i ∉ U := by
      simp only [U, C, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
    have hiI : i ∉ I := by
      simp only [I, C, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; intro h; exact hi.2 h.2
    simp only [L, if_neg hiU, if_neg hiI]
  have hL_I : ∏ i ∈ I, L i = ∏ i ∈ I, ((P 0 i : ℝ) / ((P 0 i : ℝ) - 1)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hiU : i ∉ U := by
      simp only [U, I, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
    simp only [L, if_neg hiU, if_pos hi]
  have hL_U : ∏ i ∈ U, L i = 1 := by
    have : ∏ i ∈ U, L i = ∏ _i ∈ U, (1 : ℝ) :=
      Finset.prod_congr rfl fun i hi => by simp only [L, if_pos hi]
    rw [this, Finset.prod_const_one]
  set A : ℝ := (∏ i ∈ C, ratio (P 0 i) (E 0 i)) *
      (∏ i ∈ I, ((P 0 i : ℝ) / ((P 0 i : ℝ) - 1)))
  have hA_eq_k : A = (k : ℝ) := by
    rw [hk_eq_L, hsplit L, hL_C, hL_I, hL_U, mul_one]
  have hA_pos : (0 : ℝ) < A := by
    rw [hA_eq_k]
    exact_mod_cast hk
  have hm0 : (∏ i ∈ C, ratio (P 0 i) (E 0 i)) * (∏ i ∈ I, ratio (P 0 i) (E 0 i)) *
      (∏ i ∈ U, ratio (P 0 i) (E 0 i)) = (k : ℝ) := by
    rw [← hsplit (fun i => ratio (P 0 i) (E 0 i))]
    exact hratio_prod 0
  have hI_split : ∏ i ∈ I, ratio (P 0 i) (E 0 i) =
      (∏ i ∈ I, ((P 0 i : ℝ) / ((P 0 i : ℝ) - 1))) *
      (∏ i ∈ I, (1 - 1 / ((P 0 i : ℝ) ^ (E 0 i + 1)))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ratio_eq (hP_prime 0 i)
  have hprod_one :
      (∏ i ∈ I, (1 - 1 / ((P 0 i : ℝ) ^ (E 0 i + 1)))) *
      (∏ i ∈ U, ratio (P 0 i) (E 0 i)) = 1 := by
    have hmul : A * ((∏ i ∈ I, (1 - 1 / ((P 0 i : ℝ) ^ (E 0 i + 1)))) *
        (∏ i ∈ U, ratio (P 0 i) (E 0 i))) = A * 1 := by
      conv_rhs => rw [mul_one, hA_eq_k, ← hm0, hI_split]
      dsimp only [A]
      ring
    exact mul_left_cancel₀ hA_pos.ne' hmul
  have hI_rew : ∏ i ∈ I, (1 - 1 / ((P 0 i : ℝ) ^ (E 0 i + 1))) =
      ((∏ i ∈ I, (P 0 i ^ (E 0 i + 1) - 1) : ℕ) : ℝ) /
      ((∏ i ∈ I, P 0 i ^ (E 0 i + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hge1 : 1 ≤ P 0 i ^ (E 0 i + 1) := Nat.one_le_pow _ _ (hP_prime 0 i).pos
    have hne : ((P 0 i : ℝ) ^ (E 0 i + 1)) ≠ 0 := by
      have : (0 : ℝ) < (P 0 i : ℝ) := by exact_mod_cast (hP_prime 0 i).pos
      positivity
    rw [Nat.cast_sub hge1, Nat.cast_pow, Nat.cast_one]
    field_simp
  have hU_rew : ∏ i ∈ U, ratio (P 0 i) (E 0 i) =
      ((∏ i ∈ U, ArithmeticFunction.sigma 1 (P 0 i ^ E 0 i) : ℕ) : ℝ) /
      ((∏ i ∈ U, P 0 i ^ E 0 i : ℕ) : ℝ) := by
    dsimp only [ratio]
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod]
  have hnat_eq :
      (∏ i ∈ I, (P 0 i ^ (E 0 i + 1) - 1)) *
        (∏ i ∈ U, ArithmeticFunction.sigma 1 (P 0 i ^ E 0 i)) =
      (∏ i ∈ I, P 0 i ^ (E 0 i + 1)) * (∏ i ∈ U, P 0 i ^ E 0 i) := by
    rw [hI_rew, hU_rew, div_mul_div_comm] at hprod_one
    have hden_pos : (0 : ℝ) < ((∏ i ∈ I, P 0 i ^ (E 0 i + 1) : ℕ) : ℝ) *
        ((∏ i ∈ U, P 0 i ^ E 0 i : ℕ) : ℝ) := by
      have h1 : 0 < ∏ i ∈ I, P 0 i ^ (E 0 i + 1) :=
        Finset.prod_pos fun i _ => pow_pos (hP_prime 0 i).pos _
      have h2 : 0 < ∏ i ∈ U, P 0 i ^ E 0 i :=
        Finset.prod_pos fun i _ => pow_pos (hP_prime 0 i).pos _
      have h1r : (0 : ℝ) < ((∏ i ∈ I, P 0 i ^ (E 0 i + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      have h2r : (0 : ℝ) < ((∏ i ∈ U, P 0 i ^ E 0 i : ℕ) : ℝ) := by exact_mod_cast h2
      exact mul_pos h1r h2r
    have hreal : ((∏ i ∈ I, (P 0 i ^ (E 0 i + 1) - 1) : ℕ) : ℝ) *
        ((∏ i ∈ U, ArithmeticFunction.sigma 1 (P 0 i ^ E 0 i) : ℕ) : ℝ) =
        ((∏ i ∈ I, P 0 i ^ (E 0 i + 1) : ℕ) : ℝ) *
        ((∏ i ∈ U, P 0 i ^ E 0 i : ℕ) : ℝ) :=
      (div_eq_one_iff_eq hden_pos.ne').mp hprod_one
    exact_mod_cast hreal
  by_cases hI_ne : I.Nonempty
  · -- Case I nonempty: LHS is even, RHS is odd.
    obtain ⟨i₀, hi₀⟩ := hI_ne
    have hP_odd : ∀ i : Fin s, Odd (P 0 i) := fun i => by
      have hdvd : P 0 i ∣ f 0 := Nat.dvd_of_mem_primeFactors (hP_mem 0 i)
      rcases Nat.even_or_odd (P 0 i) with ⟨t, ht⟩ | hodd
      · obtain ⟨q, hq⟩ := hdvd
        obtain ⟨u, hu⟩ := hf_odd 0
        rw [ht] at hq
        rw [hq] at hu
        have h2 : (t + t) * q = 2 * (t * q) := by ring
        omega
      · exact hodd
    have hRHS_odd : Odd ((∏ i ∈ I, P 0 i ^ (E 0 i + 1)) * (∏ i ∈ U, P 0 i ^ E 0 i)) :=
      (odd_finset_prod I _ fun i _ => (hP_odd i).pow).mul
        (odd_finset_prod U _ fun i _ => (hP_odd i).pow)
    have hodd_pow : Odd (P 0 i₀ ^ (E 0 i₀ + 1)) := (hP_odd i₀).pow
    have hfac_even : Even (P 0 i₀ ^ (E 0 i₀ + 1) - 1) := by
      obtain ⟨t, ht⟩ := hodd_pow
      exact ⟨t, by omega⟩
    have hLHS_even : Even ((∏ i ∈ I, (P 0 i ^ (E 0 i + 1) - 1)) *
        (∏ i ∈ U, ArithmeticFunction.sigma 1 (P 0 i ^ E 0 i))) := by
      rw [← Finset.mul_prod_erase I _ hi₀]
      exact (hfac_even.mul_right _).mul_right _
    obtain ⟨a, ha⟩ := hLHS_even
    obtain ⟨b, hb⟩ := hRHS_odd
    omega
  · -- Case I empty: U is nonempty, so LHS > RHS strictly.
    have hU_ne : U.Nonempty := hIU_nonempty.resolve_left hI_ne
    rw [Finset.not_nonempty_iff_eq_empty] at hI_ne
    rw [hI_ne, Finset.prod_empty, Finset.prod_empty, one_mul, one_mul] at hnat_eq
    obtain ⟨i₀, hi₀⟩ := hU_ne
    rw [← Finset.mul_prod_erase U _ hi₀, ← Finset.mul_prod_erase U _ hi₀] at hnat_eq
    have h1 : P 0 i₀ ^ E 0 i₀ < ArithmeticFunction.sigma 1 (P 0 i₀ ^ E 0 i₀) :=
      pow_lt_sigma_prime_pow (hP_prime 0 i₀) (hE_pos 0 i₀)
    have h2 : ∏ i ∈ U.erase i₀, P 0 i ^ E 0 i ≤
        ∏ i ∈ U.erase i₀, ArithmeticFunction.sigma 1 (P 0 i ^ E 0 i) :=
      Finset.prod_le_prod' fun i _ => sigma_prime_pow_ge (hP_prime 0 i)
    have hpos : 0 < ∏ i ∈ U.erase i₀, P 0 i ^ E 0 i :=
      Finset.prod_pos fun i _ => pow_pos (hP_prime 0 i).pos _
    have hlt : P 0 i₀ ^ E 0 i₀ * (∏ i ∈ U.erase i₀, P 0 i ^ E 0 i) <
        ArithmeticFunction.sigma 1 (P 0 i₀ ^ E 0 i₀) *
          (∏ i ∈ U.erase i₀, ArithmeticFunction.sigma 1 (P 0 i ^ E 0 i)) :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 hpos) (Nat.mul_le_mul_left _ h2)
    omega

private lemma finite_odd_perfect (r k : ℕ) (hk : 1 ≤ k) :
    {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Odd n ∧ n.primeFactors.card ≤ r}.Finite := by
  have hsub : {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Odd n ∧ n.primeFactors.card ≤ r} ⊆
      ⋃ s ∈ (Finset.range (r + 1) : Finset ℕ),
        {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Odd n ∧ n.primeFactors.card = s} := by
    intro n hn
    exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hn.2.2)) ⟨hn.1, hn.2.1, rfl⟩
  exact ((Finset.range (r + 1)).finite_toSet.biUnion fun s _ =>
    finite_odd_perfect_fixed_card s k hk).subset hsub

end OMA.Erdos1053H1

theorem OMA.solution : OMA.R_Erdos1053_erdos_1053_variants_guy_R1_H2_R1.H1 := by
  intro r k hk _
  apply (OMA.Erdos1053H1.finite_odd_perfect r k (by omega)).subset
  intro n hn
  exact ⟨hn.1.1, hn.1.2.1, hn.2⟩
