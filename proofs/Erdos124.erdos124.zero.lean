import FormalConjectures.ErdosProblems.«124»

-- Problem: Erdős Problem 124 — zero
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/124.lean:48 (declaration Erdos124.erdos124.zero)
-- Credit: @Rahul-007afk (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- The exponents `k` with `d ^ k ≤ x`. -/
def OMA.Ex (d x : ℕ) : Finset ℕ := (Finset.range (x + 1)).filter (fun k => d ^ k ≤ x)

lemma OMA.mem_Ex {d : ℕ} (hd : 2 ≤ d) (x k : ℕ) : k ∈ OMA.Ex d x ↔ d ^ k ≤ x := by
  unfold OMA.Ex
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hk : k < d ^ k := Nat.lt_pow_self hd
    exact ⟨by omega, h⟩

/-- The sum of all powers of `d` that are at most `x`. -/
def OMA.G (d x : ℕ) : ℕ := ∑ k ∈ OMA.Ex d x, d ^ k

lemma OMA.Ex_mono {d : ℕ} (hd : 2 ≤ d) {x y : ℕ} (h : x ≤ y) : OMA.Ex d x ⊆ OMA.Ex d y := by
  intro k hk
  rw [OMA.mem_Ex hd] at hk ⊢
  omega

lemma OMA.G_mono {d : ℕ} (hd : 2 ≤ d) {x y : ℕ} (h : x ≤ y) : OMA.G d x ≤ OMA.G d y :=
  Finset.sum_le_sum_of_subset (OMA.Ex_mono hd h)

lemma OMA.geom (e m : ℕ) : e * ∑ k ∈ Finset.range m, (e + 1) ^ k + 1 = (e + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ, ← ih]
    ring

/-- The powers of `d` up to `x` sum to at least `x / (d - 1)`. -/
lemma OMA.le_mul_G {d : ℕ} (hd : 2 ≤ d) (x : ℕ) : x ≤ (d - 1) * OMA.G d x := by
  classical
  have hex : ∃ m, x < d ^ m := ⟨x, Nat.lt_pow_self hd⟩
  have hEx : OMA.Ex d x = Finset.range (Nat.find hex) := by
    ext k
    rw [OMA.mem_Ex hd, Finset.mem_range]
    constructor
    · intro h
      by_contra hcon
      have h1 : d ^ Nat.find hex ≤ d ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 := Nat.find_spec hex
      omega
    · intro h
      have := Nat.find_min hex h
      omega
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hg := OMA.geom e (Nat.find hex)
  have hs := Nat.find_spec hex
  unfold OMA.G
  rw [hEx]
  simp only [Nat.add_sub_cancel]
  omega

/-- Brown's criterion for the merged sequence of powers: the powers up to `x`, over all bases,
sum to at least `x`. This is where the hypothesis on the reciprocals is used. -/
lemma OMA.criterion (D : Finset ℕ) (hD : ∀ d ∈ D, 3 ≤ d)
    (hsum : 1 ≤ ∑ d ∈ D, ((d : ℚ) - 1)⁻¹) (x : ℕ) : x ≤ ∑ d ∈ D, OMA.G d x := by
  have h1 : ∀ d ∈ D, (x : ℚ) * ((d : ℚ) - 1)⁻¹ ≤ (OMA.G d x : ℚ) := by
    intro d hd
    have hd3 := hD d hd
    have hd3' : (3 : ℚ) ≤ d := by exact_mod_cast hd3
    have hpos : (0 : ℚ) < (d : ℚ) - 1 := by linarith
    have h := OMA.le_mul_G (by omega : 2 ≤ d) x
    have h' : ((x : ℕ) : ℚ) ≤ (((d - 1) * OMA.G d x : ℕ) : ℚ) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one] at h'
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  have h2 : (x : ℚ) ≤ ∑ d ∈ D, (OMA.G d x : ℚ) := by
    calc (x : ℚ) = x * 1 := by ring
      _ ≤ x * ∑ d ∈ D, ((d : ℚ) - 1)⁻¹ := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg x)
      _ = ∑ d ∈ D, (x : ℚ) * ((d : ℚ) - 1)⁻¹ := Finset.mul_sum _ _ _
      _ ≤ ∑ d ∈ D, (OMA.G d x : ℚ) := Finset.sum_le_sum h1
  exact_mod_cast h2

/-- `n` is a sum, over the bases `d ∈ D`, of distinct powers of `d` that are at most `L d`. -/
def OMA.Rep (D : Finset ℕ) (L : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ K : ℕ → Finset ℕ, (∀ d ∈ D, K d ⊆ OMA.Ex d (L d)) ∧ ∑ d ∈ D, ∑ k ∈ K d, d ^ k = n

/-- Every `n` up to the total of the allowed powers is representable. -/
def OMA.Q (D : Finset ℕ) (L : ℕ → ℕ) : Prop :=
  ∀ n, n ≤ ∑ d ∈ D, OMA.G d (L d) → OMA.Rep D L n

lemma OMA.Q_congr (D : Finset ℕ) {L L' : ℕ → ℕ} (h : ∀ d ∈ D, L d = L' d) (hQ : OMA.Q D L) :
    OMA.Q D L' := by
  intro n hn
  have hT : ∑ d ∈ D, OMA.G d (L' d) = ∑ d ∈ D, OMA.G d (L d) :=
    Finset.sum_congr rfl (fun d hd => by rw [h d hd])
  obtain ⟨K, hK, hs⟩ := hQ n (by omega)
  exact ⟨K, fun d hd => by rw [← h d hd]; exact hK d hd, hs⟩

/-- Brown's induction step: raising the threshold of one base by one keeps everything
representable, provided the new value is at most one more than the current total. -/
lemma OMA.Q_step (D : Finset ℕ) (hD : ∀ d ∈ D, 2 ≤ d) (L : ℕ → ℕ) (d0 : ℕ) (hd0 : d0 ∈ D)
    (hbal : L d0 + 1 ≤ ∑ d ∈ D, OMA.G d (L d) + 1) (hQ : OMA.Q D L) :
    OMA.Q D (Function.update L d0 (L d0 + 1)) := by
  classical
  have hd2 := hD d0 hd0
  by_cases hpow : ∃ k0, d0 ^ k0 = L d0 + 1
  · obtain ⟨k0, hk0⟩ := hpow
    have hEx : OMA.Ex d0 (L d0 + 1) = insert k0 (OMA.Ex d0 (L d0)) := by
      ext k
      rw [Finset.mem_insert, OMA.mem_Ex hd2, OMA.mem_Ex hd2]
      constructor
      · intro h
        by_cases hk : d0 ^ k = L d0 + 1
        · left
          exact Nat.pow_right_injective hd2 (hk.trans hk0.symm)
        · right
          omega
      · rintro (rfl | h)
        · omega
        · omega
    have hk0not : k0 ∉ OMA.Ex d0 (L d0) := by
      rw [OMA.mem_Ex hd2]
      omega
    have hG : OMA.G d0 (L d0 + 1) = (L d0 + 1) + OMA.G d0 (L d0) := by
      unfold OMA.G
      rw [hEx, Finset.sum_insert hk0not, hk0]
    have hrest : ∑ d ∈ D.erase d0, OMA.G d (Function.update L d0 (L d0 + 1) d) =
        ∑ d ∈ D.erase d0, OMA.G d (L d) :=
      Finset.sum_congr rfl (fun d hd => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)])
    have hT : ∑ d ∈ D, OMA.G d (Function.update L d0 (L d0 + 1) d) =
        ∑ d ∈ D, OMA.G d (L d) + (L d0 + 1) := by
      rw [← Finset.add_sum_erase D _ hd0,
        ← Finset.add_sum_erase D (fun d => OMA.G d (L d)) hd0, hrest, Function.update_self, hG]
      omega
    intro n hn
    rw [hT] at hn
    by_cases hle : n ≤ ∑ d ∈ D, OMA.G d (L d)
    · obtain ⟨K, hK, hs⟩ := hQ n hle
      refine ⟨K, fun d hd => ?_, hs⟩
      by_cases hdd : d = d0
      · rw [hdd, Function.update_self]
        exact (hK d0 hd0).trans (OMA.Ex_mono hd2 (by omega))
      · rw [Function.update_of_ne hdd]
        exact hK d hd
    · obtain ⟨K, hK, hs⟩ := hQ (n - (L d0 + 1)) (by omega)
      have hk0K : k0 ∉ K d0 := fun h => hk0not (hK d0 hd0 h)
      refine ⟨Function.update K d0 (insert k0 (K d0)), fun d hd => ?_, ?_⟩
      · by_cases hdd : d = d0
        · rw [hdd, Function.update_self, Function.update_self, hEx]
          exact Finset.insert_subset_insert _ (hK d0 hd0)
        · rw [Function.update_of_ne hdd, Function.update_of_ne hdd]
          exact hK d hd
      · have hrestK : ∑ d ∈ D.erase d0, ∑ k ∈ Function.update K d0 (insert k0 (K d0)) d, d ^ k =
            ∑ d ∈ D.erase d0, ∑ k ∈ K d, d ^ k :=
          Finset.sum_congr rfl (fun d hd => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)])
        rw [← Finset.add_sum_erase D _ hd0, Function.update_self, Finset.sum_insert hk0K, hk0,
          hrestK]
        rw [← Finset.add_sum_erase D (fun d => ∑ k ∈ K d, d ^ k) hd0] at hs
        omega
  · have hEx : OMA.Ex d0 (L d0 + 1) = OMA.Ex d0 (L d0) := by
      ext k
      rw [OMA.mem_Ex hd2, OMA.mem_Ex hd2]
      constructor
      · intro h
        have hne : d0 ^ k ≠ L d0 + 1 := fun h' => hpow ⟨k, h'⟩
        omega
      · intro h
        omega
    have hGeq : ∀ d ∈ D, OMA.G d (Function.update L d0 (L d0 + 1) d) = OMA.G d (L d) := by
      intro d hd
      by_cases hdd : d = d0
      · rw [hdd, Function.update_self]
        unfold OMA.G
        rw [hEx]
      · rw [Function.update_of_ne hdd]
    intro n hn
    rw [Finset.sum_congr rfl hGeq] at hn
    obtain ⟨K, hK, hs⟩ := hQ n hn
    refine ⟨K, fun d hd => ?_, hs⟩
    by_cases hdd : d = d0
    · rw [hdd, Function.update_self, hEx]
      exact hK d0 hd0
    · rw [Function.update_of_ne hdd]
      exact hK d hd

/-- Raising all thresholds together, one unit at a time: everything up to the total of the powers
at most `x` is representable with powers at most `x`. -/
lemma OMA.Q_const (D : Finset ℕ) (hD : ∀ d ∈ D, 3 ≤ d)
    (hsum : 1 ≤ ∑ d ∈ D, ((d : ℚ) - 1)⁻¹) : ∀ x : ℕ, OMA.Q D (fun _ => x) := by
  classical
  have hD2 : ∀ d ∈ D, 2 ≤ d := fun d hd => by
    have := hD d hd
    omega
  intro x
  induction x with
  | zero =>
    intro n hn
    have h0 : ∑ d ∈ D, OMA.G d 0 = 0 := by
      refine Finset.sum_eq_zero (fun d hd => ?_)
      unfold OMA.G
      refine Finset.sum_eq_zero (fun k hk => ?_)
      rw [OMA.mem_Ex (hD2 d hd)] at hk
      have hpos : 0 < d ^ k := Nat.pow_pos (by have := hD2 d hd; omega)
      omega
    have hn0 : n = 0 := by
      simp only [h0] at hn
      omega
    exact ⟨fun _ => ∅, fun d _ => Finset.empty_subset _, by simp [hn0]⟩
  | succ x ih =>
    have inner : OMA.Q D (fun d => if d ∈ D then x + 1 else x) := by
      refine Finset.induction_on'
        (motive := fun E => OMA.Q D (fun d => if d ∈ E then x + 1 else x)) D ?_ ?_
      · simpa using ih
      · intro a E haD hED haE hQE
        have h1 := OMA.criterion D hD hsum x
        have h2 : ∑ d ∈ D, OMA.G d x ≤ ∑ d ∈ D, OMA.G d (if d ∈ E then x + 1 else x) :=
          Finset.sum_le_sum (fun d hd => OMA.G_mono (hD2 d hd) (by split_ifs <;> omega))
        have hLa : (fun d => if d ∈ E then x + 1 else x) a = x := by simp [haE]
        have hbal : (fun d => if d ∈ E then x + 1 else x) a + 1 ≤
            ∑ d ∈ D, OMA.G d ((fun d => if d ∈ E then x + 1 else x) d) + 1 := by
          rw [hLa]
          show x + 1 ≤ ∑ d ∈ D, OMA.G d (if d ∈ E then x + 1 else x) + 1
          omega
        have hstep := OMA.Q_step D hD2 _ a haD hbal hQE
        refine OMA.Q_congr D (fun d hd => ?_) hstep
        by_cases hda : d = a
        · rw [hda, Function.update_self]
          simp [haE]
        · rw [Function.update_of_ne hda]
          simp [Finset.mem_insert, hda]
    exact OMA.Q_congr D (fun d hd => by simp [hd]) inner

theorem OMA.solution : type_of% @Erdos124.erdos124.zero := by
  intro D hD hsum
  refine Filter.Eventually.of_forall (fun n => ?_)
  obtain ⟨K, hK, hs⟩ := OMA.Q_const D hD hsum n n (OMA.criterion D hD hsum n)
  rw [Set.mem_finsetSum]
  exact ⟨fun d => ∑ k ∈ K d, d ^ k, fun {d} hd => ⟨K d, fun i _ => Nat.zero_le i, rfl⟩, hs⟩
