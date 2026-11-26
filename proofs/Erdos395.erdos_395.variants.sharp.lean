import FormalConjectures.ErdosProblems.«395»

/-! Two balanced groups of orthogonal unit vectors give the sharp probability order. -/

open Erdos395

lemma OMA.central_probability_sq (j : ℕ) :
    (2 * (j : ℝ) + 1) * ((Nat.centralBinom j : ℝ) / 4 ^ j) ^ 2 ≤ 1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hrec : ((j : ℝ) + 1) * (Nat.centralBinom (j + 1) : ℝ) =
        2 * (2 * (j : ℝ) + 1) * (Nat.centralBinom j : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ j
    have hstep : (Nat.centralBinom (j + 1) : ℝ) / 4 ^ (j + 1) =
        ((2 * (j : ℝ) + 1) / (2 * ((j : ℝ) + 1))) * ((Nat.centralBinom j : ℝ) / 4 ^ j) := by
      rw [pow_succ]
      have hpow : (0 : ℝ) < 4 ^ j := by positivity
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      field_simp
      linarith only [hrec]
    have hfactor : (2 * ((j : ℝ) + 1) + 1) *
        ((2 * (j : ℝ) + 1) / (2 * ((j : ℝ) + 1))) ^ 2 ≤ 2 * (j : ℝ) + 1 := by
      have hd : (0 : ℝ) < (2 * ((j : ℝ) + 1)) ^ 2 := by positivity
      rw [div_pow, ← mul_div_assoc]
      apply (div_le_iff₀ hd).mpr
      nlinarith only [show (0 : ℝ) ≤ 2 * (j : ℝ) + 1 by positivity]
    change (2 * ((j + 1 : ℕ) : ℝ) + 1) * ((Nat.centralBinom (j + 1) : ℝ) / 4 ^ (j + 1)) ^ 2 ≤ 1
    rw [hstep, Nat.cast_add, Nat.cast_one, mul_pow, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)).trans ih

lemma OMA.choose_probability_sq (m k : ℕ) :
    ((m : ℝ) + 1) * ((m.choose k : ℝ) / 2 ^ m) ^ 2 ≤ 4 := by
  let j := (m + 1) / 2
  let p : ℝ := (Nat.centralBinom j : ℝ) / 4 ^ j
  have hlo : m ≤ 2 * j := by dsimp [j]; omega
  have hhi : 2 * j ≤ m + 1 := by dsimp [j]; omega
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hchoose : m.choose k ≤ Nat.centralBinom j :=
    (Nat.choose_le_choose k hlo).trans (Nat.choose_le_centralBinom k j)
  have hpow : (4 : ℝ) ^ j ≤ 2 * 2 ^ m := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) hhi
  have hpr : (m.choose k : ℝ) / 2 ^ m ≤ 2 * p := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      (m.choose k : ℝ) ≤ (Nat.centralBinom j : ℝ) := by exact_mod_cast hchoose
      _ = p * 4 ^ j := by
        dsimp [p]
        field_simp
      _ ≤ p * (2 * 2 ^ m) := mul_le_mul_of_nonneg_left hpow hp
      _ = 2 * p * 2 ^ m := by ring
  have hsize : (m : ℝ) + 1 ≤ 2 * (j : ℝ) + 1 := by
    have hcast : (m : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hlo
    linarith
  have hbase : (2 * (j : ℝ) + 1) * p ^ 2 ≤ 1 := OMA.central_probability_sq j
  calc
    ((m : ℝ) + 1) * ((m.choose k : ℝ) / 2 ^ m) ^ 2 ≤
        (2 * (j : ℝ) + 1) * (2 * p) ^ 2 :=
      mul_le_mul hsize (pow_le_pow_left₀ (by positivity) hpr 2) (by positivity) (by positivity)
    _ = 4 * ((2 * (j : ℝ) + 1) * p ^ 2) := by ring
    _ ≤ 4 := by linarith only [hbase]

def OMA.plus_positions (m : ℕ) (ε : Fin m → ℤ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ε i = 1)

def OMA.middle_sets (m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.powersetCard (m / 2) ∪ Finset.univ.powersetCard (m / 2 + 1)

lemma OMA.plus_in_middle (m : ℕ) (ε : Fin m → ℤ) (hε : ∀ i, ε i = -1 ∨ ε i = 1)
    (hlo : -1 ≤ ∑ i, ε i) (hhi : (∑ i, ε i) ≤ 1) :
    OMA.plus_positions m ε ∈ OMA.middle_sets m := by
  have hs : (∑ i, ε i) = 2 * ((OMA.plus_positions m ε).card : ℤ) - (m : ℤ) := by
    calc
      (∑ i, ε i) = ∑ i, (2 * (if ε i = 1 then 1 else 0) - 1 : ℤ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases hε i with h | h <;> simp [h]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
        simp [OMA.plus_positions]
  rw [hs] at hlo hhi
  have hcard : (OMA.plus_positions m ε).card = m / 2 ∨
      (OMA.plus_positions m ε).card = m / 2 + 1 := by omega
  simpa [OMA.middle_sets, Finset.mem_powersetCard] using hcard

lemma OMA.middle_sets_card (m : ℕ) :
    (OMA.middle_sets m).card ≤ 2 * m.choose (m / 2) := by
  unfold OMA.middle_sets
  refine (Finset.card_union_le _ _).trans ?_
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hk := Nat.choose_le_middle (m / 2 + 1) m
  omega

lemma OMA.middle_sets_probability_sq (m : ℕ) :
    ((m : ℝ) + 1) * (((OMA.middle_sets m).card : ℝ) / 2 ^ m) ^ 2 ≤ 16 := by
  have hcount : ((OMA.middle_sets m).card : ℝ) ≤ 2 * (m.choose (m / 2) : ℝ) := by
    exact_mod_cast OMA.middle_sets_card m
  have hprob : ((OMA.middle_sets m).card : ℝ) / 2 ^ m ≤
      2 * ((m.choose (m / 2) : ℝ) / 2 ^ m) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hcount (by positivity)
  have hb := OMA.choose_probability_sq m (m / 2)
  calc
    ((m : ℝ) + 1) * (((OMA.middle_sets m).card : ℝ) / 2 ^ m) ^ 2 ≤
        ((m : ℝ) + 1) * (2 * ((m.choose (m / 2) : ℝ) / 2 ^ m)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hprob 2) (by positivity)
    _ = 4 * (((m : ℝ) + 1) * ((m.choose (m / 2) : ℝ) / 2 ^ m) ^ 2) := by ring
    _ ≤ 16 := by linarith only [hb]

lemma OMA.int_abs_small (x : ℤ) (hx : |(x : ℝ)| ≤ √(2 : ℝ)) : -1 ≤ x ∧ x ≤ 1 := by
  have hs : √(2 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (hx.trans_lt hs)
  norm_cast at hlo hhi
  omega

lemma OMA.plus_positions_inj {m : ℕ} {ε δ : Fin m → ℤ}
    (hε : ∀ i, ε i = -1 ∨ ε i = 1) (hδ : ∀ i, δ i = -1 ∨ δ i = 1)
    (h : OMA.plus_positions m ε = OMA.plus_positions m δ) : ε = δ := by
  funext i
  have heq : (ε i = 1) ↔ (δ i = 1) := by
    simpa only [OMA.plus_positions, Finset.mem_filter, Finset.mem_univ, true_and] using
      Iff.of_eq (congrArg (fun Q : Finset (Fin m) => i ∈ Q) h)
  have h1 := hε i
  have h2 := hδ i
  omega

lemma OMA.complex_sign_bound (m k n : ℕ) (h : m + k = n) :
    ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) ∧
      signedSumCount z √(2 : ℝ) ≤ (OMA.middle_sets m).card * (OMA.middle_sets k).card := by
  classical
  let e : Fin m ⊕ Fin k ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  let z (i : Fin n) : ℂ := Sum.elim (fun _ => 1) (fun _ => Complex.I) (e.symm i)
  have hzL (i : Fin m) : z (e (Sum.inl i)) = 1 := by simp [z]
  have hzR (i : Fin k) : z (e (Sum.inr i)) = Complex.I := by simp [z]
  refine ⟨z, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := e.surjective i
    cases j with
    | inl j => simp [hzL]
    | inr j => simp [hzR]
  let S : Set (Fin n → ℤ) := {ε | (∀ i, ε i = -1 ∨ ε i = 1) ∧
      ‖∑ i, (ε i : ℂ) * z i‖ ≤ √(2 : ℝ)}
  let T := ((OMA.middle_sets m : Finset (Finset (Fin m))) : Set (Finset (Fin m))) ×ˢ
      ((OMA.middle_sets k : Finset (Finset (Fin k))) : Set (Finset (Fin k)))
  let f (ε : Fin n → ℤ) : Finset (Fin m) × Finset (Fin k) :=
    (OMA.plus_positions m (fun i => ε (e (Sum.inl i))),
      OMA.plus_positions k (fun i => ε (e (Sum.inr i))))
  have hsum (ε : Fin n → ℤ) : (∑ i, (ε i : ℂ) * z i) =
      (∑ i : Fin m, (ε (e (Sum.inl i)) : ℂ)) +
      ∑ i : Fin k, (ε (e (Sum.inr i)) : ℂ) * Complex.I := by
    calc
      _ = ∑ j : Fin m ⊕ Fin k, (ε (e j) : ℂ) * z (e j) :=
        (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
      _ = _ := by simp [Fintype.sum_sum_type, hzL, hzR]
  have hf (ε : Fin n → ℤ) (hε : ε ∈ S) : f ε ∈ T := by
    let u : ℤ := ∑ i : Fin m, ε (e (Sum.inl i))
    let v : ℤ := ∑ i : Fin k, ε (e (Sum.inr i))
    have hreal : (∑ i, (ε i : ℂ) * z i).re = (u : ℝ) := by
      rw [hsum]
      simp [u, Complex.add_re, Complex.re_sum, Complex.mul_re]
    have himag : (∑ i, (ε i : ℂ) * z i).im = (v : ℝ) := by
      rw [hsum]
      simp [v, Complex.add_im, Complex.im_sum, Complex.mul_im]
    have hu : |(u : ℝ)| ≤ √(2 : ℝ) := by
      rw [← hreal]
      exact (Complex.abs_re_le_norm _).trans hε.2
    have hv : |(v : ℝ)| ≤ √(2 : ℝ) := by
      rw [← himag]
      exact (Complex.abs_im_le_norm _).trans hε.2
    obtain ⟨hl, hr⟩ := OMA.int_abs_small u hu
    obtain ⟨hl', hr'⟩ := OMA.int_abs_small v hv
    exact Set.mk_mem_prod (OMA.plus_in_middle m _ (fun i => hε.1 _) hl hr)
      (OMA.plus_in_middle k _ (fun i => hε.1 _) hl' hr')
  have hinj : Set.InjOn f S := by
    intro ε hε δ hδ heq
    have hL := OMA.plus_positions_inj (fun i : Fin m => hε.1 (e (Sum.inl i)))
      (fun i : Fin m => hδ.1 (e (Sum.inl i))) (congrArg Prod.fst heq)
    have hR := OMA.plus_positions_inj (fun i : Fin k => hε.1 (e (Sum.inr i)))
      (fun i : Fin k => hδ.1 (e (Sum.inr i))) (congrArg Prod.snd heq)
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    cases j with
    | inl j => exact congrFun hL j
    | inr j => exact congrFun hR j
  have hfin : T.Finite := (OMA.middle_sets m).finite_toSet.prod (OMA.middle_sets k).finite_toSet
  have ht : T.ncard = (OMA.middle_sets m).card * (OMA.middle_sets k).card := by
    simp [T, Set.ncard_prod]
  exact (Set.ncard_le_ncard_of_injOn f hf hinj hfin).trans_eq ht

theorem OMA.solution : type_of% @Erdos395.erdos_395.variants.sharp := by
  refine ⟨32, ?_⟩
  intro n hn
  let m := n / 2
  let k := n - m
  have hmk : m + k = n := by dsimp [m, k]; omega
  obtain ⟨z, hz, hc⟩ := OMA.complex_sign_bound m k n hmk
  refine ⟨z, hz, ?_⟩
  let a := ((OMA.middle_sets m).card : ℝ) / (2 : ℝ) ^ m
  let b := ((OMA.middle_sets k).card : ℝ) / (2 : ℝ) ^ k
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc' : (signedSumCount z √(2 : ℝ) : ℝ) ≤
      ((OMA.middle_sets m).card : ℝ) * ((OMA.middle_sets k).card : ℝ) := by exact_mod_cast hc
  have hcount : (signedSumCount z √(2 : ℝ) : ℝ) / 2 ^ n ≤ a * b := by
    dsimp [a, b]
    rw [div_mul_div_comm, ← pow_add, hmk]
    exact div_le_div_of_nonneg_right hc' (by positivity)
  have hA : ((m : ℝ) + 1) * a ^ 2 ≤ 16 := OMA.middle_sets_probability_sq m
  have hB : ((k : ℝ) + 1) * b ^ 2 ≤ 16 := OMA.middle_sets_probability_sq k
  have hprod : ((m : ℝ) + 1) * ((k : ℝ) + 1) * (a * b) ^ 2 ≤ 16 * 16 := by
    have h := mul_le_mul hA hB (mul_nonneg (by positivity) (sq_nonneg b)) (by norm_num)
    calc
      ((m : ℝ) + 1) * ((k : ℝ) + 1) * (a * b) ^ 2 =
          (((m : ℝ) + 1) * a ^ 2) * (((k : ℝ) + 1) * b ^ 2) := by ring
      _ ≤ 16 * 16 := h
  have hm : (n : ℝ) ≤ 2 * ((m : ℝ) + 1) := by
    exact_mod_cast (show n ≤ 2 * (m + 1) by dsimp [m]; omega)
  have hk : (n : ℝ) ≤ 2 * ((k : ℝ) + 1) := by
    exact_mod_cast (show n ≤ 2 * (k + 1) by dsimp [m, k]; omega)
  have hnℝ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn2 : (n : ℝ) ^ 2 ≤ 4 * (((m : ℝ) + 1) * ((k : ℝ) + 1)) := by
    calc
      (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) := sq _
      _ ≤ (2 * ((m : ℝ) + 1)) * (2 * ((k : ℝ) + 1)) :=
        mul_le_mul hm hk hnℝ.le (by positivity)
      _ = _ := by ring
  have hbound : ((n : ℝ) * (a * b)) ^ 2 ≤ (32 : ℝ) ^ 2 := by
    calc
      ((n : ℝ) * (a * b)) ^ 2 = (n : ℝ) ^ 2 * (a * b) ^ 2 := mul_pow _ _ _
      _ ≤ (4 * (((m : ℝ) + 1) * ((k : ℝ) + 1))) * (a * b) ^ 2 :=
        mul_le_mul_of_nonneg_right hn2 (sq_nonneg _)
      _ = 4 * (((m : ℝ) + 1) * ((k : ℝ) + 1) * (a * b) ^ 2) := by ring
      _ ≤ (32 : ℝ) ^ 2 := by linarith only [hprod]
  have hp : (n : ℝ) * (a * b) ≤ 32 :=
    (sq_le_sq₀ (mul_nonneg hnℝ.le (mul_nonneg ha hb)) (by norm_num)).mp hbound
  refine hcount.trans ((le_div_iff₀ hnℝ).mpr ?_)
  simpa only [mul_comm (a * b)] using hp