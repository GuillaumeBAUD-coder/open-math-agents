import OMAStatements.S_oeis_a300591
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

-- Credit: @HBreitkreutz
namespace OMA.A300591Proof

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The Euler derivative multiplies the coefficient in degree n by n. -/
noncomputable def euler (f : PowerSeries R) : PowerSeries R :=
  X * derivative R f

lemma euler_coeff (f : PowerSeries R) (n : ℕ) :
    coeff n (euler f) = (n : R) * coeff n f := by
  cases n with
  | zero => simp [euler, coeff_zero_X_mul]
  | succ n =>
    rw [euler, coeff_succ_X_mul, coeff_derivative, Nat.cast_succ]
    ring

lemma euler_X : euler (X : PowerSeries R) = X := by simp [euler]

lemma euler_add (f g : PowerSeries R) : euler (f + g) = euler f + euler g := by
  simp [euler, mul_add]

lemma euler_sub (f g : PowerSeries R) : euler (f - g) = euler f - euler g := by
  simp [euler, mul_sub]

lemma euler_mul (f g : PowerSeries R) :
    euler (f * g) = euler f * g + f * euler g := by
  simp only [euler, Derivation.leibniz, smul_eq_mul]
  ring

noncomputable def exponential (g : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  subst (C (n : ℚ) * g) (PowerSeries.exp ℚ)

lemma exponential_zero (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    coeff 0 (exponential g n) = 1 := by
  let t := C (n : ℚ) * g
  have ht : constantCoeff t = 0 := by simp [t, hg]
  have hs : HasSubst t := HasSubst.of_constantCoeff_zero ht
  have h1 : subst t (1 : PowerSeries ℚ) = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have he : constantCoeff (PowerSeries.exp ℚ - 1) = 0 := by simp [constantCoeff_exp]
  have h := constantCoeff_subst_eq_zero (a := t) ht _ he
  change constantCoeff (subst t (PowerSeries.exp ℚ - 1)) = 0 at h
  rw [subst_sub hs, h1, map_sub, map_one, sub_eq_zero] at h
  change coeff 0 (subst t (PowerSeries.exp ℚ)) = 1
  simpa only [coeff_zero_eq_constantCoeff] using h

lemma euler_exponential (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    euler (exponential g n) = C (n : ℚ) * (euler g * exponential g n) := by
  have ht : constantCoeff (C (n : ℚ) * g) = 0 := by simp [hg]
  have hs : HasSubst (C (n : ℚ) * g) := HasSubst.of_constantCoeff_zero ht
  unfold euler exponential
  rw [derivative_subst hs, derivative_exp, Derivation.leibniz, derivative_C]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

lemma first_product_coeff {n : ℕ} (f e : PowerSeries ℚ)
    (hf : ∀ i < n, coeff i f = 0) (he : coeff 0 e = 1) :
    coeff n (f * e) = coeff n f := by
  rw [coeff_mul, Finset.sum_eq_single (n, 0)]
  · simp [he]
  · rintro ⟨i, j⟩ hij hp
    have heq : i + j = n := by simpa using hij
    have hi : i < n := by
      by_contra! hh
      exact hp (Prod.ext (by dsimp; omega) (by dsimp; omega))
    simp [hf i hi]
  · simp

/-- A unit series in each degree gives a triangular test for a series to vanish. -/
lemma diagonal_vanish (f : PowerSeries ℚ) (e : ℕ → PowerSeries ℚ)
    (he : ∀ n, coeff 0 (e n) = 1) (hf : ∀ n, coeff n (f * e n) = 0) :
    f = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih => exact (first_product_coeff f (e n) ih (he n)).symm.trans (hf n)



/-- A triangular map with unit diagonal can be inverted one coefficient at a time. -/
noncomputable def restore (E : ℕ → PowerSeries ℚ) (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  b n - ∑ j : Fin n, restore E b j.val * coeff (n - j.val) (E n)
termination_by n
decreasing_by exact j.isLt

lemma restore_spec (E : ℕ → PowerSeries ℚ) (hE : ∀ n, coeff 0 (E n) = 1)
    (b : ℕ → ℚ) (n : ℕ) :
    coeff n ((mk (restore E b) : PowerSeries ℚ) * E n) = b n := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (mk (restore E b) : PowerSeries ℚ) * coeff j (E n)),
    Finset.sum_range_succ]
  simp only [coeff_mk, Nat.sub_self, hE, mul_one]
  rw [restore.eq_1 E b n, Fin.sum_univ_eq_sum_range
    (fun j => restore E b j * coeff (n - j) (E n)) n]
  ring

noncomputable def transfer (E : ℕ → PowerSeries ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  mk (restore E fun n => (n : ℚ) * coeff n (f * E n))

lemma transfer_spec (E : ℕ → PowerSeries ℚ) (hE : ∀ n, coeff 0 (E n) = 1)
    (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (transfer E f * E n) = (n : ℚ) * coeff n (f * E n) :=
  restore_spec E hE _ n

lemma diagonal_inj (E : ℕ → PowerSeries ℚ) (hE : ∀ n, coeff 0 (E n) = 1)
    {f g : PowerSeries ℚ} (h : ∀ n, coeff n (f * E n) = coeff n (g * E n)) :
    f = g := by
  apply sub_eq_zero.mp
  apply diagonal_vanish _ E hE
  intro n
  simp only [sub_mul, map_sub, h, sub_self]

noncomputable abbrev family (g : PowerSeries ℚ) (n : ℕ) := exponential g (n ^ 2)

lemma family_derivative (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    euler (family g n) = C ((n : ℚ) ^ 2) * (euler g * family g n) := by
  unfold family
  rw [euler_exponential g hg, Nat.cast_pow]

lemma transfer_recursion (g f : PowerSeries ℚ) (hg : constantCoeff g = 0) :
    transfer (family g) f =
      euler f + transfer (family g) (transfer (family g) (f * euler g)) := by
  have hE (n : ℕ) := exponential_zero g hg (n ^ 2)
  apply diagonal_inj (family g) hE
  intro n
  rw [add_mul, map_add, transfer_spec _ hE, transfer_spec _ hE, transfer_spec _ hE]
  have h := euler_coeff (f * family g n) n
  rw [euler_mul, map_add, family_derivative g hg,
    show f * (C ((n : ℚ) ^ 2) * (euler g * family g n)) =
      C ((n : ℚ) ^ 2) * ((f * euler g) * family g n) by ring, coeff_C_mul] at h
  linear_combination -h

lemma transfer_source (g : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hsource : ∀ n : ℕ, 0 < n → coeff n (family g n) =
      (n : ℚ) ^ 2 * coeff (n - 1) (family g n)) :
    transfer (family g) X = euler g := by
  have hE (n : ℕ) := exponential_zero g hg (n ^ 2)
  apply diagonal_inj (family g) hE
  intro n
  rw [transfer_spec _ hE]
  cases n with
  | zero => simp [euler, coeff_zero_eq_constantCoeff]
  | succ k =>
    rw [coeff_succ_X_mul]
    have h := euler_coeff (family g (k+1)) (k+1)
    rw [family_derivative g hg, coeff_C_mul, hsource (k+1) (by omega),
      Nat.add_sub_cancel] at h
    have hn : ((k+1 : ℕ) : ℚ) ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    linear_combination -h

/-- Coefficients below a given degree vanish. -/
def vanishes (f : PowerSeries ℚ) (k : ℕ) : Prop := ∀ i < k, coeff i f = 0

lemma transfer_vanishes (E : ℕ → PowerSeries ℚ) (hE : ∀ n, coeff 0 (E n) = 1)
    {f : PowerSeries ℚ} {k : ℕ} (hf : vanishes f k) : vanishes (transfer E f) k := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have prev (j : ℕ) (hj : j < i) : coeff j (transfer E f) = 0 := ih j hj (by omega)
    rw [← first_product_coeff _ (E i) prev (hE i), transfer_spec _ hE,
      first_product_coeff f (E i) (fun j hj => hf j (by omega)) (hE i), hf i hi, mul_zero]

lemma vanishes_mul_euler {f g : PowerSeries ℚ} {k : ℕ} (hf : vanishes f k) :
    vanishes (f * euler g) (k + 1) := by
  intro i hi
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a,b⟩ hab
  have hs : a+b=i := by simpa using hab
  change coeff a f * coeff b (euler g) = 0
  by_cases hz : b = 0
  · simp [hz, euler_coeff]
  · rw [hf a (by omega), zero_mul]

/-- Integrality through a finite order. -/
def integralTo (f : PowerSeries ℚ) (N : ℕ) : Prop :=
  ∀ i ≤ N, ∃ a : ℤ, coeff i f = (a : ℚ)

lemma integral_sum {α : Type*} (s : Finset α) (v : α → ℚ)
    (h : ∀ a ∈ s, ∃ b : ℤ, v a = (b : ℚ)) :
    ∃ b : ℤ, ∑ a ∈ s, v a = (b : ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨c, hc⟩ := h a (by simp)
    obtain ⟨b, hb⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    exact ⟨c+b, by rw [Finset.sum_insert ha, hc, hb, Int.cast_add]⟩

lemma integral_mul_euler {f g : PowerSeries ℚ} {N : ℕ}
    (hg : ∀ j < N, ∃ b : ℤ, coeff j g = (b : ℚ))
    (f0 : coeff 0 f = 0) (hf : integralTo f N) :
    integralTo (f * euler g) N := by
  intro i hi
  rw [coeff_mul]
  apply integral_sum
  rintro ⟨a,b⟩ hab
  have hs : a + b = i := by simpa using hab
  change ∃ z : ℤ, coeff a f * coeff b (euler g) = (z : ℚ)
  by_cases h : a = 0
  · exact ⟨0, by simp [h, f0]⟩
  · obtain ⟨u, hu⟩ := hf a (by omega)
    obtain ⟨v, hv⟩ := hg b (by omega)
    exact ⟨u*((b:ℤ)*v), by rw [euler_coeff, hu, hv]; push_cast; rfl⟩

/-- Starting one degree higher at each application makes the recursion finite.
The correction to the Euler derivative in degree i is a multiple of i squared. -/
lemma transfer_congruence (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (N : ℕ)
    (prefixInt : ∀ j < N, ∃ b : ℤ, coeff j g = (b : ℚ))
    (k : ℕ) (hk : 0 < k) (f : PowerSeries ℚ) (hf : vanishes f k)
    (hiF : integralTo f N) (i : ℕ) (hi : i ≤ N) :
    ∃ z : ℤ, coeff i (transfer (family g) f) =
      (i : ℚ) * coeff i f + (i : ℚ)^2 * (z : ℚ) := by
  have hE (j : ℕ) := exponential_zero g hg (j ^ 2)
  suffices aux : ∀ d k : ℕ, N < k+d → 0 < k →
      ∀ f : PowerSeries ℚ, vanishes f k → integralTo f N →
      ∀ i ≤ N, ∃ z : ℤ, coeff i (transfer (family g) f) =
        (i : ℚ)*coeff i f + (i : ℚ)^2*(z : ℚ) from
    aux (N+1) k (by omega) hk f hf hiF i hi
  intro d
  induction d with
  | zero =>
    intro k hbound hk f hf hiF i hi
    exact ⟨0, by rw [transfer_vanishes _ hE hf i (by omega), hf i (by omega)]; simp⟩
  | succ d ih =>
    intro k hbound hk f hf hiF i hi
    let b := f * euler g
    have bv : vanishes b (k+1) := vanishes_mul_euler hf
    have bi : integralTo b N := integral_mul_euler prefixInt (hf 0 hk) hiF
    have nextBound : N < k+1+d := by omega
    have stepB := ih (k+1) nextBound (by omega) b bv bi
    have tv := transfer_vanishes _ hE bv
    have ti : integralTo (transfer (family g) b) N := by
      intro j hj
      obtain ⟨a, ha⟩ := bi j hj
      obtain ⟨u, hu⟩ := stepB j hj
      exact ⟨(j:ℤ)*a+(j:ℤ)^2*u, by rw [hu, ha]; push_cast; rfl⟩
    obtain ⟨v, hv⟩ := ih (k+1) nextBound (by omega) _ tv ti i hi
    obtain ⟨a, ha⟩ := bi i hi
    obtain ⟨u, hu⟩ := stepB i hi
    refine ⟨a+(i:ℤ)*u+v, ?_⟩
    rw [transfer_recursion g f hg, map_add, euler_coeff]
    change (i : ℚ) * coeff i f + coeff i (transfer _ (transfer _ b)) = _
    rw [hv, hu, ha]
    push_cast
    ring

lemma coeff_X_multiple (n : ℕ) : ∃ d : ℤ,
    coeff n (X : PowerSeries ℚ) = (n : ℚ)*(d : ℚ) := by
  by_cases h : n = 1
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by simp [coeff_X, h]⟩

lemma integral_source (g : PowerSeries ℚ) (hg : constantCoeff g = 0)
    (hsource : ∀ n : ℕ, 0 < n → coeff n (family g n) =
      (n : ℚ) ^ 2 * coeff (n - 1) (family g n)) (n : ℕ) :
    ∃ z : ℤ, coeff n g = (n : ℚ) * (z : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨0, by simp [hn, coeff_zero_eq_constantCoeff, hg]⟩
    have hp : ∀ j < n, ∃ a : ℤ, coeff j g = (a : ℚ) := by
      intro j hj
      obtain ⟨z, hz⟩ := ih j hj
      exact ⟨(j:ℤ)*z, by simpa using hz⟩
    have vanishX : vanishes (X : PowerSeries ℚ) 1 := by
      intro j hj
      have : j = 0 := by omega
      simp [this]
    have intX : integralTo (X : PowerSeries ℚ) n := by
      intro j hj
      obtain ⟨d, hd⟩ := coeff_X_multiple j
      exact ⟨(j:ℤ)*d, by simpa using hd⟩
    obtain ⟨z, hz⟩ := transfer_congruence g hg n hp 1 (by omega) X vanishX intX n le_rfl
    obtain ⟨d, hd⟩ := coeff_X_multiple n
    rw [transfer_source g hg hsource, euler_coeff, hd] at hz
    refine ⟨d+z, ?_⟩
    apply mul_left_cancel₀ (show (n : ℚ) ≠ 0 by exact_mod_cast hn)
    rw [Int.cast_add]
    linear_combination hz

end OMA.A300591Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a300591.main := by
  intro g h n hn
  obtain ⟨hg, hsource⟩ := h
  have hs (k : ℕ) (hk : 0 < k) :
      PowerSeries.coeff k (OMA.A300591Proof.family g k) =
        (k : ℚ)^2 * PowerSeries.coeff (k-1) (OMA.A300591Proof.family g k) := by
    simpa only [OMA.A300591Proof.family, OMA.A300591Proof.exponential, Nat.cast_pow,
      OMA.S_oeis_a300591.expMultiple] using hsource k hk
  obtain ⟨z,hz⟩ := OMA.A300591Proof.integral_source g hg hs n
  exact ⟨(n:ℤ)*z, by simpa using hz, z, rfl⟩
