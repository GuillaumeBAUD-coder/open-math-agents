import OMAStatements.S_oeis_a191450

namespace OMA.A191450

open OMA.S_oeis_a191450
open Function

private def values (i : ℕ) : ℕ := 3*i/2

private theorem values_mono : StrictMono values := by
  intro i j hij
  unfold values
  omega

private theorem inT_iff (x : ℕ) :
    InT x ↔ 0 < x ∧ (x % 3 = 0 ∨ x % 3 = 1) := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have hr : x % 3 ≠ 2 := by
      intro he
      exact h (x/3+1) (by omega) (by omega)
    omega
  · rintro ⟨hx, hr⟩
    refine ⟨hx, ?_⟩
    intro m hm he
    omega

private theorem values_range :
    Set.range values = Set.ofPred (fun x => x % 3 = 0 ∨ x % 3 = 1) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    unfold values
    omega
  · rintro (h0 | h1)
    · refine ⟨2*(x/3), ?_⟩
      unfold values
      rw [show 3*(2*(x/3)) = 2*x by omega]
      omega
    · refine ⟨2*(x/3)+1, ?_⟩
      unfold values
      rw [show 3*(2*(x/3)+1) = 2*x+1 by omega]
      omega

private theorem positive_range :
    Set.range (fun i => values (i+1)) = Set.ofPred InT := by
  ext x
  rw [Set.mem_ofPred_eq, inT_iff]
  constructor
  · rintro ⟨i, rfl⟩
    have hp : 0 < values (i+1) := values_mono (Nat.succ_pos i)
    have hr : values (i+1) ∈ Set.range values := ⟨i+1, rfl⟩
    rw [values_range] at hr
    exact ⟨hp, hr⟩
  · rintro ⟨hx, hr⟩
    have hmem : x ∈ Set.range values := by
      rw [values_range]
      exact hr
    obtain ⟨k, hk⟩ := hmem
    have hpos : 0 < k := by
      by_contra! h
      have hz : k = 0 := by omega
      rw [hz] at hk
      change 0 = x at hk
      omega
    refine ⟨k-1, ?_⟩
    change values (k-1+1) = x
    rw [show k-1+1 = k by omega, hk]

private theorem nth_of_range {p : ℕ → Prop} {f : ℕ → ℕ} (h : StrictMono f)
    (hr : Set.range f = Set.ofPred p) : Nat.nth p = f := by
  have infinite : (Set.ofPred p).Infinite := by
    rw [← hr]
    exact Set.infinite_range_of_injective h.injective
  exact ((Nat.nth_strictMono infinite).range_inj h).mp
    ((Nat.range_nth_of_infinite infinite).trans hr.symm)

private theorem first_column (n : ℕ) (hn : 1 ≤ n) : t n = A032766 n := by
  rw [t, A032766, nth_of_range values_mono values_range,
    nth_of_range (values_mono.comp (fun _ _ h => Nat.succ_lt_succ h)) positive_range]
  change values (n-1+1) = values n
  rw [show n-1+1 = n by omega]

private theorem first_positive (n : ℕ) (hn : 1 ≤ n) : 0 < t n := by
  rw [first_column n hn, A032766, nth_of_range values_mono values_range]
  unfold values
  omega

private theorem iterate_s (x j : ℕ) (hx : 0 < x) :
    (0 < s^[j] x) ∧ 2 * ((s^[j] x : ℕ) : ℤ) - 1 = (2 * (x : ℤ) - 1) * 3^j := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hy : 0 < s^[j] x := ih.1
      have hs : ((s (s^[j] x) : ℕ) : ℤ) = 3 * ((s^[j] x : ℕ) : ℤ) - 1 := by
        change ((3 * (s^[j] x) - 1 : ℕ) : ℤ) = _
        rw [Int.natCast_sub (by omega)]
        simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      constructor
      · change 0 < 3 * (s^[j] x) - 1
        omega
      · rw [hs, pow_succ, ← mul_assoc, ← ih.2]
        ring

theorem formula (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (D n k : ℤ) = (3 + (2 * (A032766 n : ℤ) - 1) * 3 ^ k) / 6 := by
  rw [← first_column n hn]
  have hi := (iterate_s (t n) (k-1) (first_positive n hn)).2
  have hpow : (3 : ℤ)^k = 3^(k-1) * 3 := by
    conv_lhs => rw [show k = (k-1)+1 by omega]
    rw [pow_succ]
  have he : 3 + (2 * (t n : ℤ) - 1) * 3^k = 6 * (D n k : ℤ) := by
    unfold D
    rw [hpow, ← mul_assoc, ← hi]
    ring
  rw [he, Int.mul_ediv_cancel_left _ (by decide : (6 : ℤ) ≠ 0)]

end OMA.A191450

theorem OMA.solution : type_of% @OMA.S_oeis_a191450.main := OMA.A191450.formula