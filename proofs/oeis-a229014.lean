import OMAStatements.S_oeis_a229014

namespace OMA.P_oeis_a229014

open OMA.S_oeis_a229014

private lemma med3_map_mono {f : ℕ → ℕ} (hf : Monotone f) (a b c : ℕ) :
    f (med3 a b c) = med3 (f a) (f b) (f c) := by
  unfold med3; simp only [hf.map_max, hf.map_min]

private lemma med3_not_lt_two (a b c u : ℕ) (h : med3 a b c = u) :
    ¬(u < a ∧ u < b) ∧ ¬(u < b ∧ u < c) ∧ ¬(a < u ∧ b < u) ∧ ¬(b < u ∧ c < u) := by
  unfold med3 at h; omega

private def popcount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, mask => (mask % 2) + popcount k (mask / 2)

private def decCap (k : ℕ) (mask : Fin (2 ^ k)) (j : Fin k) : Bool :=
  (mask.1 / 2 ^ j.1) % 2 == 1

private def encCap (k : ℕ) (cap : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨∑ j : Fin k, if cap j then 2 ^ j.1 else 0, by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Fin.sum_univ_castSucc, pow_succ]
      have h1 := ih (fun j => cap j.castSucc)
      split_ifs <;> simp [Fin.last] at * <;> omega⟩

private lemma decCap_encCap (k : ℕ) (cap : Fin k → Bool) : decCap k (encCap k cap) = cap := by
  funext j
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    unfold decCap encCap; dsimp only
    have hsum : (∑ i : Fin (k + 1), if cap i then 2 ^ i.1 else 0) =
        (∑ i : Fin k, if cap i.castSucc then 2 ^ i.1 else 0) + (if cap (Fin.last k) then 2 ^ k else 0) :=
      Fin.sum_univ_castSucc _
    rw [hsum]
    have hlt : (∑ i : Fin k, if cap i.castSucc then 2 ^ i.1 else 0) < 2 ^ k := (encCap k (fun i => cap i.castSucc)).2
    refine Fin.lastCases ?_ ?_ j
    · simp only [Fin.val_last]
      by_cases hc : cap (Fin.last k) = true
      · rw [if_pos hc]
        have hdiv : ((∑ i : Fin k, if cap i.castSucc then 2 ^ i.1 else 0) + 2 ^ k) / 2 ^ k = 1 := by
          rw [Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt hlt]
        rw [hdiv]; simp [hc]
      · simp only [Bool.not_eq_true] at hc
        rw [hc, if_neg (by decide), add_zero, Nat.div_eq_of_lt hlt]; simp
    · intro i
      simp only [Fin.val_castSucc]
      have hdvd : 2 ^ i.1 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have h2k : 2 ^ k / 2 ^ i.1 = 2 ^ (k - i.1) := Nat.pow_div (by omega) (by omega)
      have heven : 2 ∣ 2 ^ (k - i.1) := dvd_pow_self 2 (by omega)
      have hmod : (((∑ t : Fin k, if cap t.castSucc then 2 ^ t.1 else 0) +
          (if cap (Fin.last k) then 2 ^ k else 0)) / 2 ^ i.1) % 2 =
          ((∑ t : Fin k, if cap t.castSucc then 2 ^ t.1 else 0) / 2 ^ i.1) % 2 := by
        split_ifs
        · rw [Nat.add_div_of_dvd_left hdvd, h2k, Nat.add_mod, Nat.mod_eq_zero_of_dvd heven, add_zero, Nat.mod_mod]
        · simp
      rw [hmod]
      exact ih (fun t => cap t.castSucc) i

private lemma encCap_decCap (k : ℕ) (mask : Fin (2 ^ k)) : encCap k (decCap k mask) = mask := by
  apply Fin.ext
  induction k with
  | zero => have := mask.2; simp at this; omega
  | succ k ih =>
    unfold encCap decCap; dsimp only
    rw [Fin.sum_univ_castSucc]
    dsimp only [Fin.val_castSucc, Fin.val_last]
    have hhi : mask.1 / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (by simpa [pow_succ, mul_comm] using mask.2)
    have hlo : mask.1 % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
    have hsub : ∀ i : Fin k, (mask.1 / 2 ^ i.1) % 2 = ((mask.1 % 2 ^ k) / 2 ^ i.1) % 2 := by
      intro i
      have h1 : mask.1 = mask.1 % 2 ^ k + (mask.1 / 2 ^ k) * 2 ^ k := by rw [mul_comm]; exact (Nat.mod_add_div mask.1 (2 ^ k)).symm
      have hdvd : 2 ^ i.1 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have h2k : 2 ^ k / 2 ^ i.1 = 2 ^ (k - i.1) := Nat.pow_div (by omega) (by omega)
      have heven : 2 ∣ (mask.1 / 2 ^ k) * 2 ^ (k - i.1) := dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) _
      conv_lhs => rw [h1, Nat.add_div_of_dvd_left (dvd_mul_of_dvd_right hdvd _), Nat.mul_div_assoc _ hdvd, h2k, Nat.add_mod, Nat.mod_eq_zero_of_dvd heven, add_zero, Nat.mod_mod]
    simp_rw [hsub]
    have hih := ih ⟨mask.1 % 2 ^ k, hlo⟩
    unfold encCap decCap at hih; dsimp only at hih
    rw [hih]
    have hdiv : mask.1 = mask.1 % 2 ^ k + 2 ^ k * (mask.1 / 2 ^ k) := (Nat.mod_add_div mask.1 (2 ^ k)).symm
    rcases (show mask.1 / 2 ^ k = 0 ∨ mask.1 / 2 ^ k = 1 by cases hq : mask.1 / 2 ^ k with | zero => left; rfl | succ m => right; omega) with h0 | h1
    · rw [h0] at hdiv; simp [h0]; omega
    · rw [h1] at hdiv; simp [h1]; omega

private lemma popcount_eq_card (k : ℕ) (mask : Fin (2 ^ k)) :
    popcount k mask.1 = (Finset.univ.filter (fun j : Fin k => decCap k mask j = true)).card := by
  induction k with
  | zero => simp [popcount]
  | succ k ih =>
    unfold popcount
    have hlo : mask.1 / 2 < 2 ^ k := by
      have hm : mask.1 < 2 * 2 ^ k := by simpa [pow_succ'] using mask.2
      omega
    rw [ih ⟨mask.1 / 2, hlo⟩]
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
    dsimp only [decCap, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one]
    have hshift : ∀ i : Fin k, mask.1 / 2 ^ (i.1 + 1) = (mask.1 / 2) / 2 ^ i.1 := by
      intro i; rw [show 2 ^ (i.1 + 1) = 2 * 2 ^ i.1 by ring, Nat.div_div_eq_div_mul]
    simp_rw [hshift]
    by_cases h0 : mask.1 % 2 = 0
    · simp [h0]
    · have h1 : mask.1 % 2 = 1 := by omega
      simp [h1]

private def decYC (k : ℕ) (code : Fin (k ^ 4)) (i : Fin 4) : Fin k :=
  ⟨(code.1 / k ^ i.1) % k, Nat.mod_lt _ (by
    by_contra h0; push Not at h0
    have hk0 : k = 0 := by omega
    subst hk0; have := code.2; simp at this)⟩

private def encYC (k : ℕ) (_hk : 1 ≤ k) (yc : Fin 4 → Fin k) : Fin (k ^ 4) :=
  ⟨∑ i : Fin 4, (yc i).1 * k ^ i.1, by
    have hgen : ∀ (r : ℕ) (f : Fin r → Fin k), (∑ i : Fin r, (f i).1 * k ^ i.1) < k ^ r := by
      intro r f
      induction r with
      | zero => simp
      | succ r ih =>
        rw [Fin.sum_univ_castSucc, pow_succ]
        have h1 := ih (fun i => f i.castSucc)
        have h2 : (f (Fin.last r)).1 + 1 ≤ k := (f (Fin.last r)).2
        have h3 : ((f (Fin.last r)).1 + 1) * k ^ r ≤ k * k ^ r := Nat.mul_le_mul_right _ h2
        have h4 : (f (Fin.last r)).1 * k ^ r + k ^ r = ((f (Fin.last r)).1 + 1) * k ^ r := by ring
        have h5 : k * k ^ r = k ^ r * k := mul_comm _ _
        simp only [Fin.val_castSucc, Fin.val_last]
        omega
    exact hgen 4 yc⟩

private lemma decYC_encYC (k : ℕ) (hk : 1 ≤ k) (yc : Fin 4 → Fin k) : decYC k (encYC k hk yc) = yc := by
  funext i
  apply Fin.ext
  unfold decYC encYC; dsimp only
  have hlt_all : ∀ (s : ℕ) (g : Fin s → Fin k), (∑ j : Fin s, (g j).1 * k ^ j.1) < k ^ s := by
    intro s g; induction s with
    | zero => simp
    | succ s ihs =>
      rw [Fin.sum_univ_castSucc, pow_succ]
      have h1 := ihs (fun j => g j.castSucc)
      have h2 : (g (Fin.last s)).1 + 1 ≤ k := (g (Fin.last s)).2
      have h3 : ((g (Fin.last s)).1 + 1) * k ^ s ≤ k * k ^ s := Nat.mul_le_mul_right _ h2
      have h4 : (g (Fin.last s)).1 * k ^ s + k ^ s = ((g (Fin.last s)).1 + 1) * k ^ s := by ring
      have h5 : k * k ^ s = k ^ s * k := mul_comm _ _
      simp only [Fin.val_castSucc, Fin.val_last]
      omega
  have hgen : ∀ (r : ℕ) (f : Fin r → Fin k) (i : Fin r), ((∑ j : Fin r, (f j).1 * k ^ j.1) / k ^ i.1) % k = (f i).1 := by
    intro r f i
    induction r with
    | zero => exact Fin.elim0 i
    | succ r ih =>
      rw [Fin.sum_univ_castSucc]
      have hlt : (∑ j : Fin r, (f j.castSucc).1 * k ^ j.1) < k ^ r := hlt_all r (fun j => f j.castSucc)
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.val_last, Fin.val_castSucc]
        rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hlt, zero_add]
        exact Nat.mod_eq_of_lt (f (Fin.last r)).2
      · intro i'
        simp only [Fin.val_castSucc, Fin.val_last]
        have hdvd : k ^ i'.1 ∣ k ^ r := Nat.pow_dvd_pow k (by omega)
        have hkr : k ^ r / k ^ i'.1 = k ^ (r - i'.1) := Nat.pow_div (by omega) (by omega)
        have hkdvd : k ∣ (f (Fin.last r)).1 * k ^ (r - i'.1) := dvd_mul_of_dvd_right (dvd_pow_self k (by omega)) _
        rw [Nat.add_div_of_dvd_left (dvd_mul_of_dvd_right hdvd _), Nat.mul_div_assoc _ hdvd, hkr,
            Nat.add_mod, Nat.mod_eq_zero_of_dvd hkdvd, add_zero, Nat.mod_mod]
        exact ih (fun j => f j.castSucc) i'
  exact hgen 4 yc i

private lemma encYC_decYC (k : ℕ) (hk : 1 ≤ k) (code : Fin (k ^ 4)) : encYC k hk (decYC k code) = code := by
  apply Fin.ext
  unfold encYC decYC; dsimp only
  have hgen : ∀ (r : ℕ) (x : ℕ), x < k ^ r → (∑ i : Fin r, ((x / k ^ i.1) % k) * k ^ i.1) = x := by
    intro r
    induction r with
    | zero => intro x hx; simp at hx ⊢; omega
    | succ r ih =>
      intro x hx
      rw [Fin.sum_univ_castSucc]
      dsimp only [Fin.val_castSucc, Fin.val_last]
      have hlo : x % k ^ r < k ^ r := Nat.mod_lt _ (Nat.pow_pos (by omega))
      have hhi : x / k ^ r < k := by rw [pow_succ] at hx; exact Nat.div_lt_of_lt_mul (by linarith)
      have hsub : ∀ i : Fin r, (x / k ^ i.1) % k = ((x % k ^ r) / k ^ i.1) % k := by
        intro i
        have h1 : x = x % k ^ r + (x / k ^ r) * k ^ r := by rw [mul_comm]; exact (Nat.mod_add_div x (k ^ r)).symm
        have hdvd : k ^ i.1 ∣ k ^ r := Nat.pow_dvd_pow k (by omega)
        have hkr : k ^ r / k ^ i.1 = k ^ (r - i.1) := Nat.pow_div (by omega) (by omega)
        have hkdvd : k ∣ (x / k ^ r) * k ^ (r - i.1) := dvd_mul_of_dvd_right (dvd_pow_self k (by omega)) _
        conv_lhs => rw [h1, Nat.add_div_of_dvd_left (dvd_mul_of_dvd_right hdvd _), Nat.mul_div_assoc _ hdvd, hkr, Nat.add_mod, Nat.mod_eq_zero_of_dvd hkdvd, add_zero, Nat.mod_mod]
      simp_rw [hsub]
      rw [ih (x % k ^ r) hlo, Nat.mod_eq_of_lt hhi, mul_comm (x / k ^ r), Nat.mod_add_div]
  exact hgen 4 code.1 code.2

private def isSurj (k : ℕ) (yc : Fin 4 → Fin k) : Prop :=
  ∀ c : Fin k, ∃ i : Fin 4, yc i = c

private instance (k : ℕ) (yc : Fin 4 → Fin k) : Decidable (isSurj k yc) := by
  unfold isSurj; infer_instance

private def vComp (k : ℕ) (cap : Fin (k + 1) → Bool) (j : Fin k) : ℕ :=
  j.1 + ∑ t : Fin (k + 1), if t.1 ≤ j.1 ∧ cap t then 1 else 0

private def NComp (k : ℕ) (cap : Fin (k + 1) → Bool) : ℕ :=
  k - 1 + ∑ t : Fin (k + 1), if cap t then 1 else 0

private lemma vComp_le_NComp (k : ℕ) (cap : Fin (k + 1) → Bool) (j : Fin k) :
    vComp k cap j ≤ NComp k cap := by
  unfold vComp NComp
  have h1 : (∑ t : Fin (k + 1), if t.1 ≤ j.1 ∧ cap t then 1 else 0) ≤
      ∑ t : Fin (k + 1), if cap t then 1 else 0 := by
    apply Finset.sum_le_sum; intro t _; split_ifs <;> simp_all
  have := j.2; omega

private lemma vComp_strictMono (k : ℕ) (cap : Fin (k + 1) → Bool) :
    StrictMono (vComp k cap) := by
  intro a b hab
  unfold vComp
  have h1 : (∑ t : Fin (k + 1), if t.1 ≤ a.1 ∧ cap t then 1 else 0) ≤
      ∑ t : Fin (k + 1), if t.1 ≤ b.1 ∧ cap t then 1 else 0 := by
    apply Finset.sum_le_sum; intro t _; split_ifs <;> simp_all; all_goals omega
  have : a.1 < b.1 := hab
  omega

private def yComp (k : ℕ) (_hk : 1 ≤ k) (yc : Fin 4 → Fin k) (cap : Fin (k + 1) → Bool) :
    Fin 4 → Fin (NComp k cap + 1) :=
  fun i => ⟨vComp k cap (yc i), by have := vComp_le_NComp k cap (yc i); omega⟩

-- Fast memoized List (List Bool) DP checker for isValid N y
private def getMat (M : List (List Bool)) (a b : ℕ) : Bool :=
  (M.getD a []).getD b false

private lemma getD_map_range {α : Type*} (n i : ℕ) (f : ℕ → α) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, List.getElem_range]

private def dpStep (N yi : ℕ) (cur : List (List Bool)) : List (List Bool) :=
  (List.range (N + 1)).map fun b =>
    (List.range (N + 1)).map fun c =>
      if b == c then false
      else if b < yi then
        if c < yi then false
        else if c == yi then (List.range (N + 1)).any fun a => decide (yi ≤ a) && getMat cur a b
        else getMat cur yi b
      else if yi < b then
        if yi < c then false
        else if c == yi then (List.range (N + 1)).any fun a => decide (a ≤ yi) && getMat cur a b
        else getMat cur yi b
      else
        if c < yi then (List.range (N + 1)).any fun a => decide (yi ≤ a) && getMat cur a b
        else (List.range (N + 1)).any fun a => decide (a ≤ yi) && getMat cur a b

private lemma dpStep_iff (N yi : ℕ) (hy : yi ≤ N) (cur : List (List Bool)) (b c : Fin (N + 1)) :
    getMat (dpStep N yi cur) b.1 c.1 = true ↔
    b ≠ c ∧ ∃ a : Fin (N + 1), getMat cur a.1 b.1 = true ∧ med3 a.1 b.1 c.1 = yi := by
  unfold dpStep getMat
  rw [getD_map_range _ _ _ _ b.2, getD_map_range _ _ _ _ c.2]
  by_cases hbc : b.1 = c.1
  · simp only [hbc, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, false_iff]
    rintro ⟨hne, _⟩; exact hne (Fin.ext hbc)
  · have hbc_beq : (b.1 == c.1) = false := beq_false_of_ne hbc
    rw [if_neg (by simp [hbc_beq])]
    have hne : b ≠ c := fun h => hbc (congrArg Fin.val h)
    rw [and_iff_right hne]
    by_cases hlt : b.1 < yi
    · rw [if_pos hlt]
      by_cases hclt : c.1 < yi
      · rw [if_pos hclt, Bool.false_eq_true, false_iff]
        rintro ⟨a, _, hmed⟩; unfold med3 at hmed; omega
      · rw [if_neg hclt]
        by_cases hceq : c.1 = yi
        · rw [if_pos (beq_iff_eq.mpr hceq)]
          simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨a, ha, hge, hcur⟩; exact ⟨⟨a, ha⟩, hcur, by dsimp only; unfold med3; omega⟩
          · rintro ⟨a, hcur, hmed⟩; exact ⟨a.1, a.2, by unfold med3 at hmed; omega, hcur⟩
        · rw [if_neg (by simp [hceq])]
          constructor
          · intro hcur; exact ⟨⟨yi, by omega⟩, hcur, by dsimp only; unfold med3; omega⟩
          · rintro ⟨a, hcur, hmed⟩
            have haeq : a.1 = yi := by unfold med3 at hmed; omega
            rwa [← haeq]
    · rw [if_neg hlt]
      by_cases hgt : yi < b.1
      · rw [if_pos hgt]
        by_cases hcgt : yi < c.1
        · rw [if_pos hcgt, Bool.false_eq_true, false_iff]
          rintro ⟨a, _, hmed⟩; unfold med3 at hmed; omega
        · rw [if_neg hcgt]
          by_cases hceq : c.1 = yi
          · rw [if_pos (beq_iff_eq.mpr hceq)]
            simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨a, ha, hle, hcur⟩; exact ⟨⟨a, ha⟩, hcur, by dsimp only; unfold med3; omega⟩
            · rintro ⟨a, hcur, hmed⟩; exact ⟨a.1, a.2, by unfold med3 at hmed; omega, hcur⟩
          · rw [if_neg (by simp [hceq])]
            constructor
            · intro hcur; exact ⟨⟨yi, by omega⟩, hcur, by dsimp only; unfold med3; omega⟩
            · rintro ⟨a, hcur, hmed⟩
              have haeq : a.1 = yi := by unfold med3 at hmed; omega
              rwa [← haeq]
      · rw [if_neg hgt]
        by_cases hclt : c.1 < yi
        · rw [if_pos hclt]
          simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨a, ha, hge, hcur⟩; exact ⟨⟨a, ha⟩, hcur, by dsimp only; unfold med3; omega⟩
          · rintro ⟨a, hcur, hmed⟩; exact ⟨a.1, a.2, by unfold med3 at hmed; omega, hcur⟩
        · rw [if_neg hclt]
          simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨a, ha, hle, hcur⟩; exact ⟨⟨a, ha⟩, hcur, by dsimp only; unfold med3; omega⟩
          · rintro ⟨a, hcur, hmed⟩; exact ⟨a.1, a.2, by unfold med3 at hmed; omega, hcur⟩

private def dpRun (N : ℕ) (y : Fin 4 → Fin (N + 1)) :
    (r : ℕ) → r ≤ 4 → List (List Bool)
  | 0, _ => (List.range (N + 1)).map fun a => (List.range (N + 1)).map fun b => decide (a ≠ b)
  | r + 1, hr => dpStep N (y ⟨r, by omega⟩).1 (dpRun N y r (by omega))

private def isValidDP (N : ℕ) (y : Fin 4 → Fin (N + 1)) : Bool :=
  (List.range (N + 1)).any fun b => (List.range (N + 1)).any fun c => getMat (dpRun N y 4 (le_refl _)) b c

private lemma dpRun_iff (N : ℕ) (y : Fin 4 → Fin (N + 1)) (r : ℕ) (hr : r ≤ 4) (b c : Fin (N + 1)) :
    getMat (dpRun N y r hr) b.1 c.1 = true ↔
    ∃ x : Fin (r + 2) → Fin (N + 1),
      x ⟨r, by omega⟩ = b ∧ x ⟨r + 1, by omega⟩ = c ∧
      (∀ i : Fin (r + 1), x ⟨i.1, by omega⟩ ≠ x ⟨i.1 + 1, by omega⟩) ∧
      (∀ i : Fin r, (y ⟨i.1, by omega⟩).1 = med3 (x ⟨i.1, by omega⟩).1 (x ⟨i.1 + 1, by omega⟩).1 (x ⟨i.1 + 2, by omega⟩).1) := by
  induction r generalizing b c with
  | zero =>
    unfold dpRun getMat
    rw [getD_map_range _ _ _ _ b.2, getD_map_range _ _ _ _ c.2, decide_eq_true_eq]
    constructor
    · intro hne
      refine ⟨fun i => if i.1 = 0 then b else c, by simp, by simp, ?_, fun i => Fin.elim0 i⟩
      intro i; fin_cases i; intro h; exact hne (congrArg Fin.val h)
    · rintro ⟨x, hx0, hx1, hne, _⟩
      have := hne ⟨0, by omega⟩; dsimp at this; rw [← hx0, ← hx1]; exact fun h => this (Fin.ext h)
  | succ r ih =>
    unfold dpRun
    rw [dpStep_iff N (y ⟨r, by omega⟩).1 (by have := (y ⟨r, by omega⟩).2; omega)]
    constructor
    · rintro ⟨hbc, a, hcur, hmed⟩
      obtain ⟨x0, hx0a, hx0b, hne0, hmed0⟩ := (ih (by omega) a b).mp hcur
      refine ⟨Fin.snoc x0 c, ?_, ?_, ?_, ?_⟩
      · have : (⟨r + 1, by omega⟩ : Fin (r + 3)) = (⟨r + 1, by omega⟩ : Fin (r + 2)).castSucc := rfl
        rw [this, Fin.snoc_castSucc]; exact hx0b
      · have : (⟨r + 2, by omega⟩ : Fin (r + 3)) = Fin.last (r + 2) := Fin.ext (by simp [Fin.last])
        rw [this, Fin.snoc_last]
      · intro i
        by_cases hi : i.1 < r + 1
        · have e1 : (⟨i.1, by omega⟩ : Fin (r + 3)) = (⟨i.1, by omega⟩ : Fin (r + 2)).castSucc := rfl
          have e2 : (⟨i.1 + 1, by omega⟩ : Fin (r + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (r + 2)).castSucc := rfl
          rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hne0 ⟨i.1, hi⟩
        · have hi' : i.1 = r + 1 := by omega
          have e1 : (⟨i.1, by omega⟩ : Fin (r + 3)) = (⟨r + 1, by omega⟩ : Fin (r + 2)).castSucc := Fin.ext (by dsimp; omega)
          have e2 : (⟨i.1 + 1, by omega⟩ : Fin (r + 3)) = Fin.last (r + 2) := Fin.ext (by simp [Fin.last]; omega)
          rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_last, hx0b]; exact hbc
      · intro i
        by_cases hi : i.1 < r
        · have e1 : (⟨i.1, by omega⟩ : Fin (r + 3)) = (⟨i.1, by omega⟩ : Fin (r + 2)).castSucc := rfl
          have e2 : (⟨i.1 + 1, by omega⟩ : Fin (r + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (r + 2)).castSucc := rfl
          have e3 : (⟨i.1 + 2, by omega⟩ : Fin (r + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (r + 2)).castSucc := rfl
          rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hmed0 ⟨i.1, hi⟩
        · have hi' : i.1 = r := by omega
          have e0 : (⟨i.1, by omega⟩ : Fin 4) = ⟨r, by omega⟩ := Fin.ext (by dsimp; omega)
          have e1 : (⟨i.1, by omega⟩ : Fin (r + 3)) = (⟨r, by omega⟩ : Fin (r + 2)).castSucc := Fin.ext (by dsimp; omega)
          have e2 : (⟨i.1 + 1, by omega⟩ : Fin (r + 3)) = (⟨r + 1, by omega⟩ : Fin (r + 2)).castSucc := Fin.ext (by dsimp; omega)
          have e3 : (⟨i.1 + 2, by omega⟩ : Fin (r + 3)) = Fin.last (r + 2) := Fin.ext (by simp [Fin.last]; omega)
          rw [e0, e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hx0a, hx0b]; exact hmed.symm
    · rintro ⟨x, hxb, hxc, hne, hmed⟩
      refine ⟨?_, x ⟨r, by omega⟩, ?_, ?_⟩
      · have := hne ⟨r + 1, by omega⟩; simpa [hxb, hxc] using this
      · exact (ih (by omega) (x ⟨r, by omega⟩) b).mpr
          ⟨fun j => x j.castSucc, rfl, hxb, fun i => hne ⟨i.1, by omega⟩, fun i => hmed ⟨i.1, by omega⟩⟩
      · have := hmed ⟨r, by omega⟩; simpa [hxb, hxc] using this.symm

private lemma isValidDP_iff (N : ℕ) (y : Fin 4 → Fin (N + 1)) :
    isValidDP N y = true ↔ isValid N y := by
  unfold isValidDP isValid
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨b, hb, c, hc, h⟩
    obtain ⟨x, _, _, hne, hmed⟩ := (dpRun_iff N y 4 (le_refl _) ⟨b, hb⟩ ⟨c, hc⟩).mp h
    exact ⟨x, hne, fun i => hmed i⟩
  · rintro ⟨x, hne, hmed⟩
    exact ⟨(x ⟨4, by omega⟩).1, (x ⟨4, by omega⟩).2, (x ⟨4 + 1, by omega⟩).1, (x ⟨4 + 1, by omega⟩).2,
      (dpRun_iff N y 4 (le_refl _) _ _).mpr ⟨x, rfl, rfl, hne, fun i => hmed i⟩⟩

-- Gap matching predicate
private def gapsMatch (n k : ℕ) (hk : 1 ≤ k) (v : Fin k → Fin (n + 1)) (cap : Fin (k + 1) → Bool) : Prop :=
  cap ⟨0, by omega⟩ = decide (0 < (v ⟨0, hk⟩).1) ∧
  (∀ j : Fin (k - 1), cap ⟨j.1 + 1, by omega⟩ = decide ((v ⟨j.1, by omega⟩).1 + 1 < (v ⟨j.1 + 1, by omega⟩).1)) ∧
  cap ⟨k, by omega⟩ = decide ((v ⟨k - 1, by omega⟩).1 < n)

private instance (n k : ℕ) (hk : 1 ≤ k) (v : Fin k → Fin (n + 1)) (cap : Fin (k + 1) → Bool) :
    Decidable (gapsMatch n k hk v cap) := by
  unfold gapsMatch; infer_instance

-- Gap-1 Compression Theorem!
private lemma isValid_iff_comp (n k : ℕ) (hk : 1 ≤ k) (v : Fin k → Fin (n + 1))
    (hv : StrictMono v) (yc : Fin 4 → Fin k) (cap : Fin (k + 1) → Bool)
    (hgm : gapsMatch n k hk v cap) :
    isValid n (fun i => v (yc i)) ↔ isValid (NComp k cap) (yComp k hk yc cap) := by
  obtain ⟨hcap0, hcap_mid, hcap_last⟩ := hgm
  constructor
  · rintro ⟨x, hx_ne, hx_med⟩
    let φ (u : ℕ) : ℕ :=
      (∑ j : Fin k, if (v j).1 < u then 1 else 0) +
      (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ u then 1 else 0)
    have hφ_mono : Monotone φ := by
      intro a b hab
      apply Nat.add_le_add <;> (apply Finset.sum_le_sum; intro j _; split_ifs <;> simp_all; all_goals omega)
    have hφ_le : ∀ u ≤ n, φ u ≤ NComp k cap := by
      intro u hu
      by_cases hlast : (v ⟨k - 1, by omega⟩).1 < u
      · have hck : cap ⟨k, by omega⟩ = true := by rw [hcap_last, decide_eq_true_eq]; omega
        have h1 : (∑ j : Fin k, if (v j).1 < u then 1 else 0) ≤ k := by
          calc _ ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum fun j _ => by split_ifs <;> omega
            _ = k := by simp
        have h2 : (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ u then 1 else 0) + 1 ≤
            ∑ t : Fin (k + 1), if cap t then 1 else 0 := by
          rw [Fin.sum_univ_castSucc]
          have h2a : (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ u then 1 else 0) ≤
              ∑ t : Fin k, if cap t.castSucc then 1 else 0 := by
            apply Finset.sum_le_sum; intro t _
            have ht : (⟨t.1, by omega⟩ : Fin (k + 1)) = t.castSucc := rfl
            rw [ht]; split_ifs <;> simp_all
          have h2b : (if cap (Fin.last k) = true then 1 else 0) = 1 := by
            have : Fin.last k = ⟨k, by omega⟩ := rfl
            rw [this, hck]; simp
          omega
        unfold φ NComp; omega
      · have h1 : (∑ j : Fin k, if (v j).1 < u then 1 else 0) ≤ k - 1 := by
          have hmem : (⟨k - 1, by omega⟩ : Fin k) ∈ Finset.univ := Finset.mem_univ _
          have hsub : (∑ j : Fin k, if (v j).1 < u then 1 else 0) =
              (∑ j ∈ Finset.univ.erase (⟨k - 1, by omega⟩ : Fin k), if (v j).1 < u then 1 else 0) +
              (if (v ⟨k - 1, by omega⟩).1 < u then 1 else 0) :=
            (Finset.sum_erase_add Finset.univ (fun j : Fin k => if (v j).1 < u then 1 else 0) hmem).symm
          rw [if_neg hlast, add_zero] at hsub
          rw [hsub]
          calc _ ≤ ∑ _j ∈ Finset.univ.erase (⟨k - 1, by omega⟩ : Fin k), 1 := Finset.sum_le_sum fun _ _ => by split_ifs <;> omega
            _ = k - 1 := by simp [Finset.card_erase_of_mem]
        have h2 : (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ u then 1 else 0) ≤
            ∑ t : Fin (k + 1), if cap t then 1 else 0 := by
          rw [Fin.sum_univ_castSucc]
          have h2a : (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ u then 1 else 0) ≤
              ∑ t : Fin k, if cap t.castSucc then 1 else 0 := by
            apply Finset.sum_le_sum; intro t _
            have ht : (⟨t.1, by omega⟩ : Fin (k + 1)) = t.castSucc := rfl
            rw [ht]; split_ifs <;> simp_all
          omega
        unfold φ NComp; omega
    have hφ_v : ∀ j : Fin k, φ (v j).1 = vComp k cap j := by
      intro j
      unfold φ vComp
      have h1 : (∑ t : Fin k, if (v t).1 < (v j).1 then 1 else 0) = j.1 := by
        have heq : (∑ t : Fin k, if (v t).1 < (v j).1 then 1 else 0) =
            (Finset.univ.filter (fun t : Fin k => t.1 < j.1)).card := by
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl; intro t _
          have hiff : (v t).1 < (v j).1 ↔ t.1 < j.1 := ⟨fun h => hv.lt_iff_lt.mp h, fun h => hv h⟩
          simp [hiff]
        rw [heq]
        have hcard : (Finset.univ.filter (fun t : Fin k => t.1 < j.1)).card = j.1 := by
          let e : {t : Fin k // t.1 < j.1} ≃ Fin j.1 :=
            ⟨fun t => ⟨t.1.1, t.2⟩, fun t => ⟨⟨t.1, by have := t.2; have := j.2; omega⟩, t.2⟩,
             fun _ => rfl, fun _ => rfl⟩
          rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fin]
        exact hcard
      have h2 : (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ (v j).1 then 1 else 0) =
          ∑ t : Fin (k + 1), if t.1 ≤ j.1 ∧ cap t then 1 else 0 := by
        rw [Fin.sum_univ_castSucc]
        have hlast0 : (if (Fin.last k).1 ≤ j.1 ∧ cap (Fin.last k) = true then 1 else 0) = 0 := by
          rw [if_neg (by simp [Fin.last])]
        rw [hlast0, add_zero]
        apply Finset.sum_congr rfl; intro t _
        have ht : (⟨t.1, by omega⟩ : Fin (k + 1)) = t.castSucc := rfl
        have hiff : (v t).1 ≤ (v j).1 ↔ t.1 ≤ j.1 := ⟨fun h => hv.le_iff_le.mp h, fun h => hv.monotone h⟩
        rw [ht]; simp only [Fin.val_castSucc, hiff, and_comm]
      rw [h1, h2]
    have hφ_gap : ∀ a b : ℕ, a < b → φ a = φ b → ∀ j : Fin k, (v j).1 < a ∨ b < (v j).1 := by
      intro a b hab hφeq j
      by_contra hnot; push Not at hnot
      obtain ⟨hja, hjb⟩ := hnot
      have h1le : (∑ t : Fin k, if (v t).1 < a then 1 else 0) ≤ ∑ t : Fin k, if (v t).1 < b then 1 else 0 :=
        Finset.sum_le_sum fun t _ => by split_ifs <;> omega
      have h2le : (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ a then 1 else 0) ≤
          ∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ b then 1 else 0 :=
        Finset.sum_le_sum fun t _ => by split_ifs <;> simp_all; all_goals omega
      by_cases hlt : (v j).1 < b
      · have h1lt : (∑ t : Fin k, if (v t).1 < a then 1 else 0) < ∑ t : Fin k, if (v t).1 < b then 1 else 0 := by
          apply Finset.sum_lt_sum (fun t _ => by split_ifs <;> omega)
          exact ⟨j, Finset.mem_univ j, by rw [if_neg (by omega), if_pos hlt]; omega⟩
        unfold φ at hφeq; omega
      · have heqb : (v j).1 = b := by omega
        by_cases hj0 : j.1 = 0
        · have hj' : j = ⟨0, hk⟩ := Fin.ext hj0
          have hc0 : cap ⟨0, by omega⟩ = true := by rw [hcap0, decide_eq_true_eq, ← hj']; omega
          have h2lt : (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ a then 1 else 0) <
              ∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ b then 1 else 0 := by
            apply Finset.sum_lt_sum (fun t _ => by split_ifs <;> simp_all; all_goals omega)
            refine ⟨j, Finset.mem_univ j, ?_⟩
            have hc' : cap ⟨j.1, by omega⟩ = true := by simpa [hj0] using hc0
            rw [if_neg (by omega), if_pos ⟨hc', by omega⟩]; omega
          unfold φ at hφeq; omega
        · let jprev : Fin k := ⟨j.1 - 1, by omega⟩
          by_cases hprev : a ≤ (v jprev).1
          · have hplt : (v jprev).1 < b := by
              have : (v jprev).1 < (v j).1 := hv (show jprev < j by simp [Fin.lt_def, jprev]; omega)
              omega
            have h1lt : (∑ t : Fin k, if (v t).1 < a then 1 else 0) < ∑ t : Fin k, if (v t).1 < b then 1 else 0 := by
              apply Finset.sum_lt_sum (fun t _ => by split_ifs <;> omega)
              exact ⟨jprev, Finset.mem_univ jprev, by rw [if_neg (by omega), if_pos hplt]; omega⟩
            unfold φ at hφeq; omega
          · have hcm : cap ⟨j.1, by omega⟩ = true := by
              have hm := hcap_mid ⟨j.1 - 1, by omega⟩
              have e1 : (⟨(j.1 - 1) + 1, by omega⟩ : Fin (k + 1)) = ⟨j.1, by omega⟩ := Fin.ext (by dsimp; omega)
              have e2 : (⟨(j.1 - 1) + 1, by omega⟩ : Fin k) = j := Fin.ext (by dsimp; omega)
              rw [e1, e2] at hm
              dsimp only at hm
              rw [hm, decide_eq_true_eq]; dsimp [jprev] at hprev; omega
            have h2lt : (∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ a then 1 else 0) <
                ∑ t : Fin k, if cap ⟨t.1, by omega⟩ ∧ (v t).1 ≤ b then 1 else 0 := by
              apply Finset.sum_lt_sum (fun t _ => by split_ifs <;> simp_all; all_goals omega)
              exact ⟨j, Finset.mem_univ j, by rw [if_neg (by omega), if_pos ⟨hcm, by omega⟩]; omega⟩
            unfold φ at hφeq; omega
    refine ⟨fun i => ⟨φ (x i).1, by have := hφ_le (x i).1 (by have := (x i).2; omega); omega⟩, ?_, ?_⟩
    · intro i heq
      have hφeq : φ (x ⟨i.1, by omega⟩).1 = φ (x ⟨i.1 + 1, by omega⟩).1 := congrArg Fin.val heq
      have hne : (x ⟨i.1, by omega⟩).1 ≠ (x ⟨i.1 + 1, by omega⟩).1 := fun h => hx_ne i (Fin.ext h)
      by_cases hi : i.1 < 4
      · have hm := hx_med ⟨i.1, hi⟩
        have hbad := med3_not_lt_two _ _ _ _ hm.symm
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · rcases hφ_gap _ _ hlt hφeq (yc ⟨i.1, hi⟩) with h1 | h2
          · exact hbad.1 ⟨h1, lt_trans h1 hlt⟩
          · exact hbad.2.2.1 ⟨lt_trans hlt h2, h2⟩
        · rcases hφ_gap _ _ hgt hφeq.symm (yc ⟨i.1, hi⟩) with h1 | h2
          · exact hbad.1 ⟨lt_trans h1 hgt, h1⟩
          · exact hbad.2.2.1 ⟨h2, lt_trans hgt h2⟩
      · have hi' : i.1 = 4 := by omega
        have hm := hx_med ⟨4 - 1, by omega⟩
        have hbad := med3_not_lt_two _ _ _ _ hm.symm
        have e1 : (⟨4 - 1 + 1, by omega⟩ : Fin 6) = ⟨i.1, by omega⟩ := Fin.ext (by dsimp; omega)
        have e2 : (⟨4 - 1 + 2, by omega⟩ : Fin 6) = ⟨i.1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [e1, e2] at hbad
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · rcases hφ_gap _ _ hlt hφeq (yc ⟨4 - 1, by omega⟩) with h1 | h2
          · exact hbad.2.1 ⟨h1, lt_trans h1 hlt⟩
          · exact hbad.2.2.2 ⟨lt_trans hlt h2, h2⟩
        · rcases hφ_gap _ _ hgt hφeq.symm (yc ⟨4 - 1, by omega⟩) with h1 | h2
          · exact hbad.2.1 ⟨lt_trans h1 hgt, h1⟩
          · exact hbad.2.2.2 ⟨h2, lt_trans hgt h2⟩
    · intro i
      dsimp only [yComp]
      rw [← hφ_v (yc i), ← med3_map_mono hφ_mono, ← hx_med i]
  · rintro ⟨x', hx'_ne, hx'_med⟩
    -- Backward map ψ : Fin (NComp k cap + 1) -> Fin (n + 1), strictly increasing, mapping vComp j to v j
    let cnt (w : ℕ) : ℕ := ∑ j : Fin k, if vComp k cap j < w then 1 else 0
    let ψ (w : ℕ) : ℕ :=
      if h : ∃ j : Fin k, vComp k cap j = w then (v (Classical.choose h)).1
      else if cnt w = 0 then 0
      else if hc : cnt w < k then (v ⟨cnt w - 1, by omega⟩).1 + 1
      else n
    have hcnt_le : ∀ w, cnt w ≤ k := fun w => by
      calc cnt w ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum fun _ _ => by split_ifs <;> omega
        _ = k := by simp
    have hcnt_eq : ∀ (w : ℕ) (r : ℕ), r ≤ k →
        (∀ j : Fin k, vComp k cap j < w ↔ j.1 < r) → cnt w = r := by
      intro w r hr hiff
      unfold cnt
      have heq : (∑ j : Fin k, if vComp k cap j < w then 1 else 0) =
          (Finset.univ.filter (fun j : Fin k => j.1 < r)).card := by
        rw [Finset.card_filter]; apply Finset.sum_congr rfl; intro j _; simp [hiff j]
      rw [heq]
      let e : {j : Fin k // j.1 < r} ≃ Fin r :=
        ⟨fun j => ⟨j.1.1, j.2⟩, fun j => ⟨⟨j.1, by omega⟩, j.2⟩, fun _ => rfl, fun _ => rfl⟩
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fin]
    have hvComp_step : ∀ j : Fin (k - 1),
        vComp k cap ⟨j.1 + 1, by omega⟩ = vComp k cap ⟨j.1, by omega⟩ + 1 + (if cap ⟨j.1 + 1, by omega⟩ then 1 else 0) := by
      intro j; unfold vComp
      have hdiff : (∑ t : Fin (k + 1), if t.1 ≤ j.1 + 1 ∧ cap t then 1 else 0) =
          (∑ t : Fin (k + 1), if t.1 ≤ j.1 ∧ cap t then 1 else 0) + (if cap ⟨j.1 + 1, by omega⟩ then 1 else 0) := by
        have hmem : (⟨j.1 + 1, by omega⟩ : Fin (k + 1)) ∈ Finset.univ := Finset.mem_univ _
        rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem]
        have h1 : (∑ t ∈ Finset.univ.erase (⟨j.1 + 1, by omega⟩ : Fin (k + 1)), if t.1 ≤ j.1 + 1 ∧ cap t then 1 else 0) =
            ∑ t ∈ Finset.univ.erase (⟨j.1 + 1, by omega⟩ : Fin (k + 1)), if t.1 ≤ j.1 ∧ cap t then 1 else 0 := by
          apply Finset.sum_congr rfl; intro t ht
          have hne : t.1 ≠ j.1 + 1 := fun h => (Finset.ne_of_mem_erase ht) (Fin.ext h)
          have hiff : t.1 ≤ j.1 + 1 ↔ t.1 ≤ j.1 := by omega
          simp [hiff]
        rw [h1]; by_cases hc : cap ⟨j.1 + 1, by omega⟩ = true <;> simp [hc]
      dsimp only; omega
    have hvComp_0 : vComp k cap ⟨0, hk⟩ = if cap ⟨0, by omega⟩ then 1 else 0 := by
      unfold vComp; dsimp only
      have hmem : (⟨0, by omega⟩ : Fin (k + 1)) ∈ Finset.univ := Finset.mem_univ _
      rw [← Finset.sum_erase_add _ _ hmem]
      have h0 : (∑ t ∈ Finset.univ.erase ⟨0, by omega⟩, if t.1 ≤ 0 ∧ cap t then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero; intro t ht
        have hne : t.1 ≠ 0 := fun h => (Finset.ne_of_mem_erase ht) (Fin.ext h)
        rw [if_neg (by omega)]
      rw [h0, zero_add]; simp only [le_refl, true_and, zero_add]
    have hvComp_last : vComp k cap ⟨k - 1, by omega⟩ + (if cap ⟨k, by omega⟩ then 1 else 0) = NComp k cap := by
      unfold vComp NComp; dsimp only
      have hmem : (⟨k, by omega⟩ : Fin (k + 1)) ∈ Finset.univ := Finset.mem_univ _
      have h1 : (∑ t : Fin (k + 1), if t.1 ≤ k - 1 ∧ cap t then 1 else 0) =
          ∑ t ∈ Finset.univ.erase (⟨k, by omega⟩ : Fin (k + 1)), if cap t then 1 else 0 := by
        rw [← Finset.sum_erase_add Finset.univ (fun t : Fin (k + 1) => if t.1 ≤ k - 1 ∧ cap t then 1 else 0) hmem]
        have hk0 : (if k ≤ k - 1 ∧ cap ⟨k, by omega⟩ = true then 1 else 0) = 0 := by rw [if_neg (by omega)]
        dsimp only at hk0 ⊢; rw [hk0, add_zero]
        apply Finset.sum_congr rfl; intro t ht
        have hne : t.1 ≠ k := fun h => (Finset.ne_of_mem_erase ht) (Fin.ext h)
        have hle : t.1 ≤ k - 1 := by have := t.2; omega
        simp [hle]
      have h2 := (Finset.sum_erase_add Finset.univ (fun t : Fin (k + 1) => if cap t then 1 else 0) hmem).symm
      rw [h2, ← h1]; omega
    have hψ_v : ∀ j : Fin k, ψ (vComp k cap j) = (v j).1 := by
      intro j; unfold ψ
      have hex : ∃ t : Fin k, vComp k cap t = vComp k cap j := ⟨j, rfl⟩
      rw [dif_pos hex]
      have heq : Classical.choose hex = j := (vComp_strictMono k cap).injective (Classical.choose_spec hex)
      rw [heq]
    have hψ_le : ∀ w ≤ NComp k cap, ψ w ≤ n := by
      intro w _
      unfold ψ
      split_ifs with h1 h2 h3
      · have := (v (Classical.choose h1)).2; omega
      · omega
      · have hlt_next : (v ⟨cnt w - 1, by omega⟩).1 < (v ⟨cnt w, h3⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
        have := (v ⟨cnt w, h3⟩).2; omega
      · omega
    -- Show ψ is strictly increasing on [0, NComp k cap] by showing ψ w < ψ (w + 1) for w < NComp k cap
    have hψ_step : ∀ w < NComp k cap, ψ w < ψ (w + 1) := by
      intro w hw
      by_cases h1 : ∃ j : Fin k, vComp k cap j = w
      · obtain ⟨j, rfl⟩ := h1
        rw [hψ_v j]
        by_cases h2 : ∃ j' : Fin k, vComp k cap j' = vComp k cap j + 1
        · obtain ⟨j', hj'⟩ := h2
          rw [← hj', hψ_v j']
          exact hv ((vComp_strictMono k cap).lt_iff_lt.mp (by omega))
        · unfold ψ; rw [dif_neg h2]
          have hcw : cnt (vComp k cap j + 1) = j.1 + 1 := by
            apply hcnt_eq _ _ (by have := j.2; omega)
            intro t; constructor
            · intro hlt
              by_contra hge
              have hle : vComp k cap j ≤ vComp k cap t := (vComp_strictMono k cap).monotone (Fin.le_def.mpr (by omega))
              have : vComp k cap t = vComp k cap j := by omega
              have : t = j := (vComp_strictMono k cap).injective this
              subst this; omega
            · intro hlt
              have : vComp k cap t ≤ vComp k cap j := (vComp_strictMono k cap).monotone (Fin.le_def.mpr (by omega))
              omega
          simp only [hcw, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
          by_cases hlt : j.1 + 1 < k
          · rw [dif_pos hlt]
            have hj_eq : (⟨j.1 + 1 - 1, by omega⟩ : Fin k) = j := Fin.ext (by simp)
            simp only [hj_eq]; omega
          · rw [dif_neg hlt]
            have hjlast : j = ⟨k - 1, by omega⟩ := Fin.ext (by have := j.2; dsimp; omega)
            rw [hjlast]
            have hck : cap ⟨k, by omega⟩ = true := by
              by_contra hcf; simp only [Bool.not_eq_true] at hcf; rw [hcf] at hvComp_last; simp at hvComp_last
              rw [hjlast] at hw; omega
            rw [hcap_last, decide_eq_true_eq] at hck; exact hck
      · -- w is NOT a vComp j, so w is a gap element -> w + 1 MUST be a vComp j!
        have h2 : ∃ j' : Fin k, vComp k cap j' = w + 1 := by
          by_cases hw0 : w = 0
          · subst hw0
            have hc0 : cap ⟨0, by omega⟩ = true := by
              by_contra hcf; simp only [Bool.not_eq_true] at hcf; rw [hcf] at hvComp_0; simp at hvComp_0
              exact h1 ⟨⟨0, hk⟩, hvComp_0⟩
            refine ⟨⟨0, hk⟩, ?_⟩; rw [hvComp_0, hc0]; simp
          · have hr_pos : 0 < cnt w := by
              by_contra h0
              have hc0 : cnt w = 0 := by omega
              have hv0 : ¬(vComp k cap ⟨0, hk⟩ < w) := by
                intro hlt
                have hge : 1 ≤ cnt w := by
                  have hmem : (⟨0, hk⟩ : Fin k) ∈ Finset.univ := Finset.mem_univ _
                  have := Finset.single_le_sum (f := fun j : Fin k => if vComp k cap j < w then 1 else 0) (fun _ _ => Nat.zero_le _) hmem
                  rw [if_pos hlt] at this; exact this
                omega
              have : vComp k cap ⟨0, hk⟩ ≤ 1 := by rw [hvComp_0]; split_ifs <;> omega
              have : vComp k cap ⟨0, hk⟩ ≠ w := fun h => h1 ⟨⟨0, hk⟩, h⟩
              omega
            have hr_lt : cnt w < k := by
              by_contra hge
              have hck : cnt w = k := by have := hcnt_le w; omega
              have hlast_lt : vComp k cap ⟨k - 1, by omega⟩ < w := by
                by_contra hno
                have hmem : (⟨k - 1, by omega⟩ : Fin k) ∈ Finset.univ := Finset.mem_univ _
                have hsub : cnt w = (∑ j ∈ Finset.univ.erase (⟨k - 1, by omega⟩ : Fin k), if vComp k cap j < w then 1 else 0) +
                    (if vComp k cap ⟨k - 1, by omega⟩ < w then 1 else 0) :=
                  (Finset.sum_erase_add Finset.univ (fun j : Fin k => if vComp k cap j < w then 1 else 0) hmem).symm
                rw [if_neg hno, add_zero] at hsub
                have : cnt w ≤ k - 1 := by
                  rw [hsub]
                  calc _ ≤ ∑ _j ∈ Finset.univ.erase (⟨k - 1, by omega⟩ : Fin k), 1 := Finset.sum_le_sum fun _ _ => by split_ifs <;> omega
                    _ = k - 1 := by simp [Finset.card_erase_of_mem]
                omega
              have : NComp k cap ≤ vComp k cap ⟨k - 1, by omega⟩ + 1 := by rw [← hvComp_last]; split_ifs <;> omega
              omega
            have hlt_prev : vComp k cap ⟨cnt w - 1, by omega⟩ < w := by
              by_contra hno
              have hall : ∀ j : Fin k, vComp k cap j < w → j.1 < cnt w - 1 := by
                intro j hj
                by_contra hge
                have hle_j : (⟨cnt w - 1, by omega⟩ : Fin k) ≤ j := Fin.le_def.mpr (by dsimp; omega)
                have := (vComp_strictMono k cap).monotone hle_j
                omega
              have hle : cnt w ≤ cnt w - 1 := by
                have hsub : (Finset.univ.filter (fun j : Fin k => vComp k cap j < w)).card ≤
                    (Finset.univ.filter (fun j : Fin k => j.1 < cnt w - 1)).card :=
                  Finset.card_le_card fun j hj => by
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hall j hj
                have hcard : (Finset.univ.filter (fun j : Fin k => j.1 < cnt w - 1)).card = cnt w - 1 := by
                  let e : {j : Fin k // j.1 < cnt w - 1} ≃ Fin (cnt w - 1) :=
                    ⟨fun j => ⟨j.1.1, j.2⟩, fun j => ⟨⟨j.1, by omega⟩, j.2⟩, fun _ => rfl, fun _ => rfl⟩
                  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fin]
                rw [hcard, Finset.card_filter] at hsub; dsimp only [cnt]; omega
              omega
            have hge_cur : w < vComp k cap ⟨cnt w, hr_lt⟩ := by
              by_contra hno
              have hne : vComp k cap ⟨cnt w, hr_lt⟩ ≠ w := fun h => h1 ⟨⟨cnt w, hr_lt⟩, h⟩
              have hlt' : vComp k cap ⟨cnt w, hr_lt⟩ < w := by omega
              have hge : cnt w + 1 ≤ cnt w := by
                have hsub : (Finset.univ.filter (fun j : Fin k => j.1 < cnt w + 1)).card ≤
                    (Finset.univ.filter (fun j : Fin k => vComp k cap j < w)).card :=
                  Finset.card_le_card fun j hj => by
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
                    have := (vComp_strictMono k cap).monotone (Fin.le_def.mpr (by dsimp; omega : j.1 ≤ (⟨cnt w, hr_lt⟩ : Fin k).1))
                    omega
                have hcard : (Finset.univ.filter (fun j : Fin k => j.1 < cnt w + 1)).card = cnt w + 1 := by
                  let e : {j : Fin k // j.1 < cnt w + 1} ≃ Fin (cnt w + 1) :=
                    ⟨fun j => ⟨j.1.1, j.2⟩, fun j => ⟨⟨j.1, by omega⟩, j.2⟩, fun _ => rfl, fun _ => rfl⟩
                  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fin]
                rw [hcard, Finset.card_filter] at hsub; dsimp only [cnt]; omega
              omega
            have hstep := hvComp_step ⟨cnt w - 1, by omega⟩
            dsimp only at hstep
            have e1 : (⟨cnt w - 1 + 1, by omega⟩ : Fin k) = ⟨cnt w, hr_lt⟩ := Fin.ext (by dsimp; omega)
            rw [e1] at hstep
            refine ⟨⟨cnt w, hr_lt⟩, ?_⟩
            split_ifs at hstep <;> omega
        obtain ⟨j', hj'⟩ := h2
        rw [← hj', hψ_v j']
        unfold ψ; rw [dif_neg h1]
        by_cases hc0 : cnt w = 0
        · rw [if_pos hc0]
          have h0 : 0 < (v ⟨0, hk⟩).1 := by
            have hcap0' : cap ⟨0, by omega⟩ = true := by
              by_contra hcf; simp only [Bool.not_eq_true] at hcf; rw [hcf] at hvComp_0; simp at hvComp_0
              by_cases hw0 : w = 0
              · exact h1 ⟨⟨0, hk⟩, by omega⟩
              · have : 1 ≤ cnt w := by
                  have hmem : (⟨0, hk⟩ : Fin k) ∈ Finset.univ := Finset.mem_univ _
                  have := Finset.single_le_sum (f := fun j : Fin k => if vComp k cap j < w then 1 else 0) (fun _ _ => Nat.zero_le _) hmem
                  rw [if_pos (by omega)] at this; exact this
                omega
            rwa [hcap0, decide_eq_true_eq] at hcap0'
          have := hv.monotone (show (⟨0, hk⟩ : Fin k) ≤ j' by simp [Fin.le_def])
          omega
        · rw [if_neg hc0]
          have hcw : cnt w = j'.1 := by
            apply hcnt_eq _ _ (by have := j'.2; omega)
            intro t; constructor
            · intro hlt
              have : vComp k cap t < vComp k cap j' := by omega
              exact (vComp_strictMono k cap).lt_iff_lt.mp this
            · intro hlt
              have hlt' : vComp k cap t < vComp k cap j' := hvComp_strictMono_aux (vComp_strictMono k cap) hlt
              have hne : vComp k cap t ≠ w := fun h => h1 ⟨t, h⟩
              omega
          have hlt : cnt w < k := by have := j'.2; omega
          rw [dif_pos hlt]
          have hm := hcap_mid ⟨j'.1 - 1, by omega⟩
          have hcm : cap ⟨j'.1 - 1 + 1, by omega⟩ = true := by
            have hst := hvComp_step ⟨j'.1 - 1, by omega⟩
            have e1 : (⟨j'.1 - 1 + 1, by omega⟩ : Fin k) = j' := Fin.ext (by dsimp; omega)
            rw [e1] at hst
            have hne : vComp k cap ⟨j'.1 - 1, by omega⟩ ≠ w := fun h => h1 ⟨_, h⟩
            by_contra hcf; simp only [Bool.not_eq_true] at hcf; rw [hcf] at hst; simp at hst; omega
          rw [hcm] at hm
          have hgap := (decide_eq_true_eq.mp hm.symm)
          have e1 : (⟨cnt w - 1, by omega⟩ : Fin k) = ⟨j'.1 - 1, by omega⟩ := Fin.ext (by dsimp; omega)
          have e2 : (⟨j'.1 - 1 + 1, by omega⟩ : Fin k) = j' := Fin.ext (by dsimp; omega)
          rw [e2] at hgap; rw [e1]; exact hgap
    have hψ_strict : ∀ a b : ℕ, a < b → b ≤ NComp k cap → ψ a < ψ b := by
      intro a b hab hb
      induction b with
      | zero => omega
      | succ b ih =>
        by_cases heq : a = b
        · subst heq; exact hψ_step a (by omega)
        · exact lt_trans (ih (by omega) (by omega)) (hψ_step b (by omega))
    have hψ_mono_on : ∀ a b c : ℕ, a ≤ NComp k cap → b ≤ NComp k cap → c ≤ NComp k cap →
        ψ (med3 a b c) = med3 (ψ a) (ψ b) (ψ c) := by
      intro a b c ha hb hc
      have hle : ∀ u v : ℕ, u ≤ v → v ≤ NComp k cap → ψ u ≤ ψ v := fun u v huv hv => by
        rcases eq_or_lt_of_le huv with rfl | hlt
        · exact le_refl _
        · exact le_of_lt (hψ_strict u v hlt hv)
      have hmin : ∀ u v : ℕ, u ≤ NComp k cap → v ≤ NComp k cap → ψ (min u v) = min (ψ u) (ψ v) := fun u v hu hv => by
        rcases le_total u v with h | h
        · rw [min_eq_left h, min_eq_left (hle u v h hv)]
        · rw [min_eq_right h, min_eq_right (hle v u h hu)]
      have hmax : ∀ u v : ℕ, u ≤ NComp k cap → v ≤ NComp k cap → ψ (max u v) = max (ψ u) (ψ v) := fun u v hu hv => by
        rcases le_total u v with h | h
        · rw [max_eq_right h, max_eq_right (hle u v h hv)]
        · rw [max_eq_left h, max_eq_left (hle v u h hu)]
      unfold med3
      rw [hmax _ _ (le_trans (min_le_left _ _) ha) (le_trans (min_le_right _ _) hc),
          hmin _ _ ha hb, hmin _ _ (max_le ha hb) hc, hmax _ _ ha hb]
    refine ⟨fun i => ⟨ψ (x' i).1, by have := hψ_le (x' i).1 (by have := (x' i).2; omega); omega⟩, ?_, ?_⟩
    · intro i heq
      have hval : ψ (x' ⟨i.1, by omega⟩).1 = ψ (x' ⟨i.1 + 1, by omega⟩).1 := congrArg Fin.val heq
      have hne : (x' ⟨i.1, by omega⟩).1 ≠ (x' ⟨i.1 + 1, by omega⟩).1 := fun h => hx'_ne i (Fin.ext h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd hval (ne_of_lt (hψ_strict _ _ hlt (by have := (x' ⟨i.1 + 1, by omega⟩).2; omega)))
      · exact absurd hval (ne_of_gt (hψ_strict _ _ hgt (by have := (x' ⟨i.1, by omega⟩).2; omega)))
    · intro i
      dsimp only
      rw [← hψ_mono_on _ _ _ (by have := (x' ⟨i.1, by omega⟩).2; omega)
          (by have := (x' ⟨i.1 + 1, by omega⟩).2; omega) (by have := (x' ⟨i.1 + 2, by omega⟩).2; omega),
          ← hx'_med i]
      exact (hψ_v (yc i)).symm
where
  hvComp_strictMono_aux {k : ℕ} {f : Fin k → ℕ} (hf : StrictMono f) {a b : Fin k} (h : a.1 < b.1) : f a < f b :=
    hf h

-- Stars-and-bars count of {v : Fin k -> Fin (n+1) // StrictMono v ∧ gapsMatch n k hk v cap}
private def gapCard (n k c1 : ℕ) : ℕ :=
  if c1 = 0 then (if n + 1 = k then 1 else 0)
  else if k + c1 ≤ n + 1 then Nat.choose (n - k) (c1 - 1) else 0

-- Bijection: compositions of S into r positive parts bounded by M (S ≤ M) has cardinality Nat.choose (S - 1) (r - 1)
private lemma card_pos_comp (M S r : ℕ) (hSM : S ≤ M) (hr : 1 ≤ r) (hS : r ≤ S) :
    Fintype.card {g : Fin r → Fin (M + 1) // (∀ i, 1 ≤ (g i).1) ∧ (∑ i : Fin r, (g i).1) = S} =
    Nat.choose (S - 1) (r - 1) := by
  induction r generalizing S with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero =>
      simp only [Nat.sub_self, Nat.choose_zero_right]
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨fun _ => ⟨S, by omega⟩, fun _ => hS, by simp⟩, ?_⟩
      rintro ⟨g, _, hsum⟩; apply Subtype.ext; funext i; fin_cases i; apply Fin.ext; simpa using hsum
    | succ r =>
      let φ : {g : Fin (r + 2) → Fin (M + 1) // (∀ i, 1 ≤ (g i).1) ∧ (∑ i : Fin (r + 2), (g i).1) = S} →
          (Σ t : Fin (S - (r + 1)), {g0 : Fin (r + 1) → Fin (M + 1) //
            (∀ i, 1 ≤ (g0 i).1) ∧ (∑ i : Fin (r + 1), (g0 i).1) = S - (t.1 + 1)}) :=
        fun ⟨g, hg, hsum⟩ =>
          have hlast_ge : 1 ≤ (g (Fin.last (r + 1))).1 := hg _
          have hinit_ge : r + 1 ≤ ∑ i : Fin (r + 1), (g i.castSucc).1 := by
            calc r + 1 = ∑ _i : Fin (r + 1), 1 := by simp
              _ ≤ ∑ i : Fin (r + 1), (g i.castSucc).1 := Finset.sum_le_sum fun i _ => hg i.castSucc
          have hsum' : (∑ i : Fin (r + 1), (g i.castSucc).1) + (g (Fin.last (r + 1))).1 = S := by
            rwa [Fin.sum_univ_castSucc] at hsum
          ⟨⟨(g (Fin.last (r + 1))).1 - 1, by omega⟩,
           ⟨fun i => g i.castSucc, fun i => hg i.castSucc, by dsimp only; omega⟩⟩
      have hbij : Function.Bijective φ := by
        constructor
        · rintro ⟨g1, hg1, hs1⟩ ⟨g2, hg2, hs2⟩ heq
          have ht : (g1 (Fin.last (r + 1))).1 - 1 = (g2 (Fin.last (r + 1))).1 - 1 :=
            congrArg (fun x => x.1.1) heq
          have hlast : g1 (Fin.last (r + 1)) = g2 (Fin.last (r + 1)) := Fin.ext (by
            have := hg1 (Fin.last (r + 1)); have := hg2 (Fin.last (r + 1)); omega)
          have hinit : ∀ i : Fin (r + 1), g1 i.castSucc = g2 i.castSucc := by
            intro i
            have := congrArg (fun x => x.2.1 i) heq
            exact this
          apply Subtype.ext; funext i; refine Fin.lastCases hlast hinit i
        · rintro ⟨t, ⟨g0, hg0, hs0⟩⟩
          let gfull : Fin (r + 2) → Fin (M + 1) :=
            Fin.snoc g0 ⟨t.1 + 1, by have := t.2; omega⟩
          refine ⟨⟨gfull, ?_, ?_⟩, ?_⟩
          · intro i; refine Fin.lastCases ?_ ?_ i
            · dsimp [gfull]; rw [Fin.snoc_last]; dsimp only; omega
            · intro j; dsimp [gfull]; rw [Fin.snoc_castSucc]; exact hg0 j
          · rw [Fin.sum_univ_castSucc]; dsimp [gfull]; rw [Fin.snoc_last]
            have : (∑ i : Fin (r + 1), ((Fin.snoc g0 ⟨t.1 + 1, by have := t.2; omega⟩ : Fin (r + 2) → Fin (M + 1)) i.castSucc).1) =
                ∑ i : Fin (r + 1), (g0 i).1 := by
              apply Finset.sum_congr rfl; intro i _; rw [Fin.snoc_castSucc]
            rw [this, hs0]; have := t.2; dsimp only; omega
          · refine Sigma.ext (Fin.ext (by dsimp [φ, gfull]; rw [Fin.snoc_last]; dsimp only; omega)) ?_
            have hval : (fun i : Fin (r + 1) => gfull i.castSucc) = g0 := by
              funext i; dsimp [gfull]; exact Fin.snoc_castSucc _ _ i
            have hsig : ∀ (n1 n2 : ℕ) (_ : n1 = n2)
                (x : {g0 : Fin (r + 1) → Fin (M + 1) // (∀ i, 1 ≤ (g0 i).1) ∧ (∑ i : Fin (r + 1), (g0 i).1) = S - (n1 + 1)})
                (y : {g0 : Fin (r + 1) → Fin (M + 1) // (∀ i, 1 ≤ (g0 i).1) ∧ (∑ i : Fin (r + 1), (g0 i).1) = S - (n2 + 1)}),
                x.1 = y.1 → HEq x y := by
              rintro n1 _ rfl ⟨x, _⟩ ⟨y, _⟩ hxy; subst hxy; rfl
            dsimp only [φ]
            exact hsig ((gfull (Fin.last (r + 1))).1 - 1) t.1 (by dsimp [gfull]; rw [Fin.snoc_last]; simp) _ _ hval
      rw [Fintype.card_congr (Equiv.ofBijective φ hbij), Fintype.card_sigma]
      have hterm : ∀ t : Fin (S - (r + 1)),
          Fintype.card {g0 : Fin (r + 1) → Fin (M + 1) // (∀ i, 1 ≤ (g0 i).1) ∧ (∑ i : Fin (r + 1), (g0 i).1) = S - (t.1 + 1)} =
          Nat.choose (S - (t.1 + 1) - 1) r := fun t => by
        have := ih (S - (t.1 + 1)) (by omega) (by omega) (by have := t.2; omega)
        simpa using this
      simp_rw [hterm]
      -- Hockey-stick identity: sum over t of C(S - t - 2, r) = C(S - 1, r + 1)
      have hhs : ∀ N : ℕ, (∑ t : Fin N, Nat.choose (r + t.1) r) = Nat.choose (r + N) (r + 1) := by
        intro N; induction N with
        | zero => simp
        | succ N ihN =>
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          rw [ihN, show r + (N + 1) = (r + N) + 1 by omega, Nat.choose_succ_succ]
          ring
      let revE : Fin (S - (r + 1)) ≃ Fin (S - (r + 1)) :=
        ⟨fun t => ⟨S - (r + 1) - 1 - t.1, by have := t.2; omega⟩,
         fun t => ⟨S - (r + 1) - 1 - t.1, by have := t.2; omega⟩,
         fun t => Fin.ext (by dsimp; have := t.2; omega),
         fun t => Fin.ext (by dsimp; have := t.2; omega)⟩
      have hrev : (∑ t : Fin (S - (r + 1)), Nat.choose (S - (t.1 + 1) - 1) r) =
          ∑ t : Fin (S - (r + 1)), Nat.choose (r + t.1) r :=
        Fintype.sum_equiv revE _ _ fun t => by congr 1; dsimp [revE]; have := t.2; omega
      rw [hrev, hhs, show r + (S - (r + 1)) = S - 1 by omega]; rfl

private lemma card_gapsMatch (n k : ℕ) (hk : 1 ≤ k) (cap : Fin (k + 1) → Bool) :
    Fintype.card {v : Fin k → Fin (n + 1) // StrictMono v ∧ gapsMatch n k hk v cap} =
    gapCard n k (Finset.univ.filter (fun t : Fin (k + 1) => cap t = true)).card := by
  let S_act := Finset.univ.filter (fun t : Fin (k + 1) => cap t = true)
  let c1 := S_act.card
  unfold gapCard
  -- Bijection between v and gap vector g : Fin (k + 1) -> ℕ with (g t > 0 ↔ cap t) and ∑ g = n + 1 - k
  by_cases hc0 : c1 = 0
  · rw [if_pos hc0]
    have hallF : ∀ t : Fin (k + 1), cap t = false := by
      intro t; by_contra h; simp only [Bool.not_eq_false] at h
      have hmem : t ∈ S_act := Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩
      have : 0 < c1 := Finset.card_pos.mpr ⟨t, hmem⟩
      omega
    by_cases hnk : n + 1 = k
    · rw [if_pos hnk, Fintype.card_eq_one_iff]
      refine ⟨⟨fun j => ⟨j.1, by omega⟩, fun a b hab => hab, ?_⟩, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [hallF]; simp
        · intro j; rw [hallF]; simp
        · rw [hallF]; simp; omega
      · rintro ⟨v, hv, h0, hmid, _⟩
        apply Subtype.ext; funext j; apply Fin.ext
        have hstep : ∀ r : ℕ, (hr : r < k) → (v ⟨r, hr⟩).1 = r := by
          intro r; induction r with
          | zero => intro hr; rw [hallF] at h0; symm at h0; simp only [decide_eq_false_iff_not, not_lt, Nat.le_zero] at h0; exact h0
          | succ r ihr =>
            intro hr
            have hm := hmid ⟨r, by omega⟩
            rw [hallF] at hm; symm at hm; simp only [decide_eq_false_iff_not, not_lt] at hm
            have hlt : (v ⟨r, by omega⟩).1 < (v ⟨r + 1, hr⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
            have := ihr (by omega); omega
        exact hstep j.1 j.2
    · rw [if_neg hnk, Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨v, hv, h0, hmid, hlast⟩ => ?_⟩
      have hstep : ∀ r : ℕ, (hr : r < k) → (v ⟨r, hr⟩).1 = r := by
        intro r; induction r with
        | zero => intro hr; rw [hallF] at h0; symm at h0; simp only [decide_eq_false_iff_not, not_lt, Nat.le_zero] at h0; exact h0
        | succ r ihr =>
          intro hr
          have hm := hmid ⟨r, by omega⟩
          rw [hallF] at hm; symm at hm; simp only [decide_eq_false_iff_not, not_lt] at hm
          have hlt : (v ⟨r, by omega⟩).1 < (v ⟨r + 1, hr⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
          have := ihr (by omega); omega
      rw [hallF] at hlast; symm at hlast; simp only [decide_eq_false_iff_not, not_lt] at hlast
      have := hstep (k - 1) (by omega); have := (v ⟨k - 1, by omega⟩).2; omega
  · rw [if_neg hc0]
    have hc1_pos : 1 ≤ c1 := by omega
    by_cases hle : k + c1 ≤ n + 1
    · rw [if_pos hle]
      -- Equivalence between valid v and positive compositions g : Fin c1 -> ℕ summing to n + 1 - k
      let emb : Fin c1 ≃o S_act := S_act.orderIsoOfFin rfl
      let gOf (v : Fin k → Fin (n + 1)) (t : Fin (k + 1)) : ℕ :=
        if h0 : t.1 = 0 then (v ⟨0, hk⟩).1
        else if hk' : t.1 < k then (v ⟨t.1, hk'⟩).1 - (v ⟨t.1 - 1, by omega⟩).1 - 1
        else n - (v ⟨k - 1, by omega⟩).1
      have hg_sum : ∀ (v : Fin k → Fin (n + 1)), StrictMono v → (∑ t : Fin (k + 1), gOf v t) = n + 1 - k := by
        intro v hv
        have hv_ge : ∀ r : ℕ, (hr : r < k) → r ≤ (v ⟨r, hr⟩).1 := by
          intro r; induction r with
          | zero => intro _; omega
          | succ r' ih' =>
            intro hr'
            have hlt' : (v ⟨r', by omega⟩).1 < (v ⟨r' + 1, hr'⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
            have := ih' (by omega); omega
        have htele : ∀ r : ℕ, (hr : r < k) → (∑ t : Fin (r + 1), gOf v ⟨t.1, by omega⟩) = (v ⟨r, hr⟩).1 - r := by
          intro r; induction r with
          | zero => intro hr; simp [gOf]
          | succ r ihr =>
            intro hr
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            rw [ihr (by omega)]
            dsimp only [gOf]
            rw [dif_neg (by omega), dif_pos hr]
            have er : (⟨r + 1 - 1, by omega⟩ : Fin k) = ⟨r, by omega⟩ := Fin.ext (by simp)
            rw [er]
            have hlt : (v ⟨r, by omega⟩).1 < (v ⟨r + 1, hr⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
            have hge : r ≤ (v ⟨r, by omega⟩).1 := hv_ge r (by omega)
            omega
        have hsum_eq : (∑ t : Fin (k + 1), gOf v t) = (∑ t : Fin k, gOf v ⟨t.1, by omega⟩) + gOf v ⟨k, by omega⟩ := by
          rw [Fin.sum_univ_castSucc]; rfl
        rw [hsum_eq]
        have hk_eq : (∑ t : Fin k, gOf v ⟨t.1, by omega⟩) = ∑ t : Fin ((k - 1) + 1), gOf v ⟨t.1, by omega⟩ := by
          refine Fintype.sum_equiv (finCongr (by omega)) _ _ fun _ => rfl
        rw [hk_eq, htele (k - 1) (by omega)]
        dsimp only [gOf]
        rw [dif_neg (by omega), dif_neg (by omega)]
        have hge : k - 1 ≤ (v ⟨k - 1, by omega⟩).1 := by
          have : ∀ r : ℕ, (hr : r < k) → r ≤ (v ⟨r, hr⟩).1 := by
            intro r; induction r with
            | zero => intro _; omega
            | succ r' ih' =>
              intro hr'
              have hlt' : (v ⟨r', by omega⟩).1 < (v ⟨r' + 1, hr'⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
              have := ih' (by omega); omega
          exact this (k - 1) (by omega)
        have hle_n : (v ⟨k - 1, by omega⟩).1 ≤ n := by have := (v ⟨k - 1, by omega⟩).2; omega
        have hstep_sub : (v ⟨k - 1, by omega⟩).1 - (k - 1) + (n - (v ⟨k - 1, by omega⟩).1) = n + 1 - k := by omega
        exact hstep_sub
      have hg_pos : ∀ (v : Fin k → Fin (n + 1)), StrictMono v → gapsMatch n k hk v cap →
          ∀ t : Fin (k + 1), (1 ≤ gOf v t ↔ cap t = true) := by
        intro v hv ⟨h0, hmid, hlast⟩ t
        unfold gOf
        split_ifs with ht0 htk
        · have ht_eq : t = ⟨0, by omega⟩ := Fin.ext ht0
          clear ht0; rw [ht_eq, h0, decide_eq_true_eq]; omega
        · have hm := hmid ⟨t.1 - 1, by omega⟩
          have e1 : (⟨t.1 - 1 + 1, by omega⟩ : Fin (k + 1)) = t := Fin.ext (by dsimp; omega)
          have e2 : (⟨t.1 - 1 + 1, by omega⟩ : Fin k) = ⟨t.1, htk⟩ := Fin.ext (by dsimp; omega)
          rw [e1, e2] at hm
          dsimp only at hm
          rw [hm, decide_eq_true_eq]
          have hlt : (v ⟨t.1 - 1, by omega⟩).1 < (v ⟨t.1, htk⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
          omega
        · have ht_eq : t = ⟨k, by omega⟩ := Fin.ext (by have := t.2; dsimp; omega)
          simp only [ht_eq, hlast, decide_eq_true_eq]
          have : (v ⟨k - 1, by omega⟩).1 ≤ n := by have := (v ⟨k - 1, by omega⟩).2; omega
          omega
      let φ : {v : Fin k → Fin (n + 1) // StrictMono v ∧ gapsMatch n k hk v cap} →
          {g : Fin c1 → Fin (n + 1 - k + 1) // (∀ i, 1 ≤ (g i).1) ∧ (∑ i : Fin c1, (g i).1) = n + 1 - k} :=
        fun ⟨v, hv, hgm⟩ =>
          ⟨fun i => ⟨gOf v (emb i).1, by
             have hle1 : gOf v (emb i).1 ≤ ∑ t : Fin (k + 1), gOf v t :=
               Finset.single_le_sum (f := gOf v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
             rw [hg_sum v hv] at hle1; omega⟩,
           fun i => (hg_pos v hv hgm (emb i).1).mpr (Finset.mem_filter.mp (emb i).2).2,
           by
             have hsum1 : (∑ i : Fin c1, gOf v (emb i).1) = ∑ t ∈ S_act, gOf v t := by
               rw [← Finset.sum_attach S_act (gOf v)]
               exact Fintype.sum_equiv emb.toEquiv _ _ fun _ => rfl
             dsimp only
             rw [hsum1, ← hg_sum v hv]
             rw [← Finset.sum_subset (Finset.subset_univ S_act)]
             intro t _ ht
             have hnot : cap t ≠ true := fun h => ht (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩)
             have := (hg_pos v hv hgm t).not.mpr hnot; omega⟩
      have hbij : Function.Bijective φ := by
        constructor
        · rintro ⟨v1, hv1, hgm1⟩ ⟨v2, hv2, hgm2⟩ heq
          have hg_eq : ∀ t : Fin (k + 1), gOf v1 t = gOf v2 t := by
            intro t
            by_cases ht : t ∈ S_act
            · have := congrArg (fun x => (x.1 (emb.symm ⟨t, ht⟩)).1) heq
              simpa [φ] using this
            · have hnot : cap t ≠ true := fun h => ht (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩)
              have h1 := (hg_pos v1 hv1 hgm1 t).not.mpr hnot
              have h2 := (hg_pos v2 hv2 hgm2 t).not.mpr hnot
              omega
          apply Subtype.ext; funext j; apply Fin.ext
          have hstep : ∀ r : ℕ, (hr : r < k) → (v1 ⟨r, hr⟩).1 = (v2 ⟨r, hr⟩).1 := by
            intro r; induction r with
            | zero => intro hr; have := hg_eq ⟨0, by omega⟩; simpa [gOf] using this
            | succ r ihr =>
              intro hr
              have hgeq := hg_eq ⟨r + 1, by omega⟩
              simp only [gOf, show r + 1 ≠ 0 by omega, hr, ↓reduceDIte, Nat.add_sub_cancel] at hgeq
              have hlt1 : (v1 ⟨r, by omega⟩).1 < (v1 ⟨r + 1, hr⟩).1 := hv1 (Fin.lt_def.mpr (by dsimp; omega))
              have hlt2 : (v2 ⟨r, by omega⟩).1 < (v2 ⟨r + 1, hr⟩).1 := hv2 (Fin.lt_def.mpr (by dsimp; omega))
              have hprev := ihr (by omega); omega
          exact hstep j.1 j.2
        · rintro ⟨g, hg, hsum⟩
          let gfull (t : Fin (k + 1)) : ℕ := if ht : t ∈ S_act then (g (emb.symm ⟨t, ht⟩)).1 else 0
          have hgfull_sum : (∑ t : Fin (k + 1), gfull t) = n + 1 - k := by
            rw [← Finset.sum_subset (Finset.subset_univ S_act) (fun t _ ht => dif_neg ht)]
            rw [← Finset.sum_coe_sort S_act gfull]
            rw [← Fintype.sum_equiv emb.toEquiv (fun i => (g i).1) (fun x => gfull x.1) (fun i => by simp [gfull])]
            exact hsum
          let v : Fin k → Fin (n + 1) := fun j =>
            ⟨j.1 + ∑ t : Fin (k + 1), if t.1 ≤ j.1 then gfull t else 0, by
              have hle' : (∑ t : Fin (k + 1), if t.1 ≤ j.1 then gfull t else 0) ≤ ∑ t : Fin (k + 1), gfull t :=
                Finset.sum_le_sum fun t _ => by split_ifs <;> omega
              have := j.2; omega⟩
          have hv_mono : StrictMono v := by
            intro a b hab
            show (v a).1 < (v b).1; dsimp [v]
            have hle' : (∑ t : Fin (k + 1), if t.1 ≤ a.1 then gfull t else 0) ≤
                ∑ t : Fin (k + 1), if t.1 ≤ b.1 then gfull t else 0 :=
              Finset.sum_le_sum fun t _ => by split_ifs <;> omega
            have : a.1 < b.1 := hab; omega
          have hgfull_eq : ∀ t : Fin (k + 1), gOf v t = gfull t := by
            intro t; unfold gOf
            split_ifs with ht0 htk
            · have ht_eq : t = ⟨0, by omega⟩ := Fin.ext ht0
              clear ht0; rw [ht_eq]; dsimp [v]
              have hmem : (⟨0, by omega⟩ : Fin (k + 1)) ∈ Finset.univ := Finset.mem_univ _
              rw [← Finset.sum_erase_add Finset.univ (fun s : Fin (k + 1) => if s.1 ≤ 0 then gfull s else 0) hmem]
              have h0 : (∑ s ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin (k + 1)), if s.1 ≤ 0 then gfull s else 0) = 0 :=
                Finset.sum_eq_zero fun s hs => by
                  have hne : s.1 ≠ 0 := fun h => (Finset.ne_of_mem_erase hs) (Fin.ext h)
                  rw [if_neg (by omega)]
              rw [h0, zero_add]; simp only [le_refl, ↓reduceIte, zero_add]
              rfl
            · dsimp [v]
              have hmem : t ∈ Finset.univ := Finset.mem_univ _
              have hdiff : (∑ s : Fin (k + 1), if s.1 ≤ t.1 then gfull s else 0) =
                  (∑ s : Fin (k + 1), if s.1 ≤ t.1 - 1 then gfull s else 0) + gfull t := by
                rw [← Finset.sum_erase_add Finset.univ (fun s : Fin (k + 1) => if s.1 ≤ t.1 then gfull s else 0) hmem,
                    ← Finset.sum_erase_add Finset.univ (fun s : Fin (k + 1) => if s.1 ≤ t.1 - 1 then gfull s else 0) hmem]
                have h1 : (∑ s ∈ Finset.univ.erase t, if s.1 ≤ t.1 then gfull s else 0) =
                    ∑ s ∈ Finset.univ.erase t, if s.1 ≤ t.1 - 1 then gfull s else 0 := by
                  apply Finset.sum_congr rfl; intro s hs
                  have hne : s.1 ≠ t.1 := fun h => (Finset.ne_of_mem_erase hs) (Fin.ext h)
                  have hiff : s.1 ≤ t.1 ↔ s.1 ≤ t.1 - 1 := by omega
                  simp [hiff]
                rw [h1, if_pos (le_refl _), if_neg (by omega), add_zero]
              rw [hdiff]; omega
            · have ht_eq : t = ⟨k, by omega⟩ := Fin.ext (by have := t.2; dsimp; omega)
              simp only [ht_eq]; dsimp [v]
              have hmem : (⟨k, by omega⟩ : Fin (k + 1)) ∈ Finset.univ := Finset.mem_univ _
              have h1 : (∑ s : Fin (k + 1), if s.1 ≤ k - 1 then gfull s else 0) + gfull ⟨k, by omega⟩ =
                  ∑ s : Fin (k + 1), gfull s := by
                rw [← Finset.sum_erase_add Finset.univ (fun s : Fin (k + 1) => if s.1 ≤ k - 1 then gfull s else 0) hmem,
                    ← Finset.sum_erase_add Finset.univ gfull hmem]
                have h2 : (∑ s ∈ Finset.univ.erase (⟨k, by omega⟩ : Fin (k + 1)), if s.1 ≤ k - 1 then gfull s else 0) =
                    ∑ s ∈ Finset.univ.erase (⟨k, by omega⟩ : Fin (k + 1)), gfull s := by
                  apply Finset.sum_congr rfl; intro s hs
                  have hne : s.1 ≠ k := fun h => (Finset.ne_of_mem_erase hs) (Fin.ext h)
                  rw [if_pos (by have := s.2; omega)]
                dsimp only; rw [h2, if_neg (by omega), add_zero]
              omega
          have hgm : gapsMatch n k hk v cap := by
            refine ⟨?_, ?_, ?_⟩
            · have h1 := hgfull_eq ⟨0, by omega⟩; dsimp [gOf] at h1
              by_cases h0 : cap ⟨0, by omega⟩ = true
              · have hmem : (0 : Fin (k + 1)) ∈ S_act := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
                have hge := hg (emb.symm ⟨0, hmem⟩)
                dsimp [gfull] at h1; rw [dif_pos hmem] at h1
                rw [h0]; symm; rw [decide_eq_true_eq]; omega
              · simp only [Bool.not_eq_true] at h0
                have hmem : (0 : Fin (k + 1)) ∉ S_act := fun h => by have := (Finset.mem_filter.mp h).2; simp_all
                dsimp [gfull] at h1; rw [dif_neg hmem] at h1
                rw [h0]; symm; rw [decide_eq_false_iff_not]; omega
            · intro j
              have h1 := hgfull_eq ⟨j.1 + 1, by have := j.2; omega⟩
              dsimp [gOf] at h1; rw [dif_pos (by have := j.2; omega)] at h1
              have hlt : (v ⟨j.1, by have := j.2; omega⟩).1 < (v ⟨j.1 + 1, by have := j.2; omega⟩).1 :=
                hv_mono (Fin.lt_def.mpr (by dsimp; omega))
              by_cases hm : cap ⟨j.1 + 1, by have := j.2; omega⟩ = true
              · have hmem : (⟨j.1 + 1, by have := j.2; omega⟩ : Fin (k + 1)) ∈ S_act := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
                have := hg (emb.symm ⟨_, hmem⟩)
                dsimp [gfull] at h1; rw [dif_pos hmem] at h1
                rw [hm]; symm; rw [decide_eq_true_eq]; omega
              · simp only [Bool.not_eq_true] at hm
                have hmem : (⟨j.1 + 1, by have := j.2; omega⟩ : Fin (k + 1)) ∉ S_act := fun h => by have := (Finset.mem_filter.mp h).2; simp_all
                dsimp [gfull] at h1; rw [dif_neg hmem] at h1
                rw [hm]; symm; rw [decide_eq_false_iff_not]; omega
            · have h1 := hgfull_eq ⟨k, by omega⟩
              simp only [gOf, show k ≠ 0 by omega, lt_irrefl, ↓reduceDIte] at h1
              have hle_n : (v ⟨k - 1, by omega⟩).1 ≤ n := by have := (v ⟨k - 1, by omega⟩).2; omega
              by_cases hl : cap ⟨k, by omega⟩ = true
              · have hmem : (⟨k, by omega⟩ : Fin (k + 1)) ∈ S_act := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
                have hge := hg (emb.symm ⟨⟨k, by omega⟩, hmem⟩)
                dsimp [gfull] at h1; rw [dif_pos hmem] at h1
                rw [hl]; symm; rw [decide_eq_true_eq]; omega
              · simp only [Bool.not_eq_true] at hl
                have hmem : (⟨k, by omega⟩ : Fin (k + 1)) ∉ S_act := fun h => by have := (Finset.mem_filter.mp h).2; simp_all
                dsimp [gfull] at h1; rw [dif_neg hmem] at h1
                rw [hl]; symm; rw [decide_eq_false_iff_not]; omega
          refine ⟨⟨v, hv_mono, hgm⟩, ?_⟩
          apply Subtype.ext; funext i; apply Fin.ext; dsimp [φ]
          rw [hgfull_eq (emb i).1]; simp [gfull, (emb i).2]
      rw [Fintype.card_congr (Equiv.ofBijective φ hbij), card_pos_comp (n + 1 - k) (n + 1 - k) c1 (le_refl _) hc1_pos (by omega)]
      congr 1; omega
    · rw [if_neg hle, Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨v, hv, hgm⟩ => ?_⟩
      let gOf (t : Fin (k + 1)) : ℕ :=
        if h0 : t.1 = 0 then (v ⟨0, hk⟩).1
        else if hk' : t.1 < k then (v ⟨t.1, hk'⟩).1 - (v ⟨t.1 - 1, by omega⟩).1 - 1
        else n - (v ⟨k - 1, by omega⟩).1
      have hge1 : ∀ t ∈ S_act, 1 ≤ gOf t := by
        intro t ht
        have hct : cap t = true := (Finset.mem_filter.mp ht).2
        obtain ⟨h0, hmid, hlast⟩ := hgm
        unfold gOf
        split_ifs with ht0 htk
        · have : t = ⟨0, by omega⟩ := Fin.ext ht0; rw [this, h0, decide_eq_true_eq] at hct; omega
        · have hm := hmid ⟨t.1 - 1, by omega⟩
          have e1 : (⟨t.1 - 1 + 1, by omega⟩ : Fin (k + 1)) = t := Fin.ext (by dsimp; omega)
          have e2 : (⟨t.1 - 1 + 1, by omega⟩ : Fin k) = ⟨t.1, htk⟩ := Fin.ext (by dsimp; omega)
          rw [e1, e2] at hm; dsimp only at hm; rw [hm, decide_eq_true_eq] at hct; omega
        · have ht_eq : t = ⟨k, by omega⟩ := Fin.ext (by have := t.2; dsimp; omega)
          simp only [ht_eq, hlast, decide_eq_true_eq] at hct; omega
      have hsum_le : (∑ t : Fin (k + 1), gOf t) ≤ n + 1 - k := by
        have hv_ge : ∀ r : ℕ, (hr : r < k) → r ≤ (v ⟨r, hr⟩).1 := by
          intro r; induction r with
          | zero => intro _; omega
          | succ r' ih' =>
            intro hr'
            have hlt' : (v ⟨r', by omega⟩).1 < (v ⟨r' + 1, hr'⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
            have := ih' (by omega); omega
        have htele : ∀ r : ℕ, (hr : r < k) → (∑ t : Fin (r + 1), gOf ⟨t.1, by omega⟩) = (v ⟨r, hr⟩).1 - r := by
          intro r; induction r with
          | zero => intro hr; simp [gOf]
          | succ r ihr =>
            intro hr; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]; rw [ihr (by omega)]
            dsimp only [gOf]; rw [dif_neg (by omega), dif_pos hr]
            have er : (⟨r + 1 - 1, by omega⟩ : Fin k) = ⟨r, by omega⟩ := Fin.ext (by simp)
            rw [er]
            have hlt : (v ⟨r, by omega⟩).1 < (v ⟨r + 1, hr⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
            have hge : r ≤ (v ⟨r, by omega⟩).1 := hv_ge r (by omega)
            omega
        have hsum_eq : (∑ t : Fin (k + 1), gOf t) = (∑ t : Fin k, gOf ⟨t.1, by omega⟩) + gOf ⟨k, by omega⟩ := by
          rw [Fin.sum_univ_castSucc]; rfl
        rw [hsum_eq]
        have hk_eq : (∑ t : Fin k, gOf ⟨t.1, by omega⟩) = ∑ t : Fin ((k - 1) + 1), gOf ⟨t.1, by omega⟩ := by
          refine Fintype.sum_equiv (finCongr (by omega)) _ _ fun _ => rfl
        rw [hk_eq, htele (k - 1) (by omega)]
        dsimp only [gOf]; rw [dif_neg (by omega), dif_neg (by omega)]
        have hge : k - 1 ≤ (v ⟨k - 1, by omega⟩).1 := by
          have : ∀ r : ℕ, (hr : r < k) → r ≤ (v ⟨r, hr⟩).1 := by
            intro r; induction r with
            | zero => intro _; omega
            | succ r' ih' =>
              intro hr'
              have hlt' : (v ⟨r', by omega⟩).1 < (v ⟨r' + 1, hr'⟩).1 := hv (Fin.lt_def.mpr (by dsimp; omega))
              have := ih' (by omega); omega
          exact this (k - 1) (by omega)
        have hle_n : (v ⟨k - 1, by omega⟩).1 ≤ n := by have := (v ⟨k - 1, by omega⟩).2; omega
        omega
      have hc1_le : c1 ≤ ∑ t : Fin (k + 1), gOf t := by
        calc c1 = ∑ _t ∈ S_act, 1 := by simp [c1]
          _ ≤ ∑ t ∈ S_act, gOf t := Finset.sum_le_sum hge1
          _ ≤ ∑ t : Fin (k + 1), gOf t := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      omega

private def wVal (k c1 : ℕ) : ℕ :=
  match k with
  | 1 => match c1 with
    | 0 => 0
    | 1 => 0
    | 2 => 1
    | _ => 0
  | 2 => match c1 with
    | 0 => 2
    | 1 => 14
    | 2 => 26
    | 3 => 14
    | _ => 0
  | 3 => match c1 with
    | 0 => 16
    | 1 => 76
    | 2 => 136
    | 3 => 108
    | 4 => 32
    | _ => 0
  | 4 => match c1 with
    | 0 => 12
    | 1 => 64
    | 2 => 136
    | 3 => 144
    | 4 => 76
    | 5 => 16
    | _ => 0
  | _ => 0

-- Pure-Nat fast evaluator for wCount (zero Finset/Fintype inside decide!)
private def dpInit (N : ℕ) : List (List Bool) :=
  (List.range (N + 1)).map fun a => (List.range (N + 1)).map fun b => decide (a ≠ b)

private def isValidDPFast (N : ℕ) (ys : List ℕ) : Bool :=
  let mat := ys.foldl (fun cur yi => dpStep N yi cur) (dpInit N)
  (List.range (N + 1)).any fun b => (List.range (N + 1)).any fun c => getMat mat b c

private def isSurjFast (k code : ℕ) : Bool :=
  (List.range k).all fun c => (List.range 4).any fun i => (code / k ^ i) % k == c

private def yListFast (k code mask : ℕ) : List ℕ :=
  (List.range 4).map fun i => let c := (code / k ^ i) % k; c + popcount (c + 1) mask

private def wCountRange (k c1 lo len : ℕ) : ℕ :=
  (List.range' lo len).foldl (fun acc code =>
    if isSurjFast k code then
      acc + (List.range (2 ^ (k + 1))).foldl (fun acc2 mask =>
        if popcount (k + 1) mask == c1 &&
           isValidDPFast (k - 1 + popcount (k + 1) mask) (yListFast k code mask)
        then acc2 + 1 else acc2) 0
    else acc) 0

private def wCountFast (k c1 : ℕ) : ℕ :=
  (List.range (k ^ 4)).foldl (fun acc code =>
    if isSurjFast k code then
      acc + (List.range (2 ^ (k + 1))).foldl (fun acc2 mask =>
        if popcount (k + 1) mask == c1 &&
           isValidDPFast (k - 1 + popcount (k + 1) mask) (yListFast k code mask)
        then acc2 + 1 else acc2) 0
    else acc) 0

private lemma wCountFast_eq_range (k c1 : ℕ) : wCountFast k c1 = wCountRange k c1 0 (k ^ 4) := by
  unfold wCountFast wCountRange; simp only [List.range_eq_range']

private lemma foldl_cond_add_shift (l : List ℕ) (p : ℕ → Bool) (f : ℕ → ℕ) (a : ℕ) :
    l.foldl (fun acc x => if p x then acc + f x else acc) a =
    a + l.foldl (fun acc x => if p x then acc + f x else acc) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split_ifs
    · rw [zero_add, ih (a + f x), ih (f x), Nat.add_assoc]
    · exact ih a

private lemma wCountRange_add (k c1 lo a b : ℕ) :
    wCountRange k c1 lo (a + b) = wCountRange k c1 lo a + wCountRange k c1 (lo + a) b := by
  unfold wCountRange
  have hlen : List.range' lo (a + b) = List.range' lo a ++ List.range' (lo + a) b := by
    simp
  rw [hlen, List.foldl_append]
  exact foldl_cond_add_shift _ _ _ _

private lemma popcount_eq_sum (r mask : ℕ) :
    popcount r mask = ∑ t : Fin r, if (mask / 2 ^ t.1) % 2 = 1 then 1 else 0 := by
  induction r generalizing mask with
  | zero => simp [popcount]
  | succ r ih =>
    rw [popcount, ih (mask / 2), Fin.sum_univ_succ]
    dsimp only [Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one]
    have hsh : ∀ i : Fin r, mask / 2 ^ (i.1 + 1) = (mask / 2) / 2 ^ i.1 := by
      intro i; rw [show 2 ^ (i.1 + 1) = 2 * 2 ^ i.1 by ring, Nat.div_div_eq_div_mul]
    simp_rw [hsh]
    by_cases h0 : mask % 2 = 0
    · simp [h0]
    · have h1 : mask % 2 = 1 := by omega
      simp [h1]

private lemma NComp_decCap_eq (k : ℕ) (mask : Fin (2 ^ (k + 1))) :
    NComp k (decCap (k + 1) mask) = k - 1 + popcount (k + 1) mask.1 := by
  unfold NComp decCap; rw [popcount_eq_sum]; congr 1
  apply Finset.sum_congr rfl; intro t _; simp

private lemma vComp_decCap_eq (k : ℕ) (mask : Fin (2 ^ (k + 1))) (j : Fin k) :
    vComp k (decCap (k + 1) mask) j = j.1 + popcount (j.1 + 1) mask.1 := by
  unfold vComp decCap; rw [popcount_eq_sum]; congr 1
  have h1 : (∑ t : Fin (k + 1), if t.1 ≤ j.1 ∧ ((mask.1 / 2 ^ t.1) % 2 == 1) = true then 1 else 0) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin (k + 1) => t.1 ≤ j.1), if (mask.1 / 2 ^ t.1) % 2 = 1 then 1 else 0 := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro t _; by_cases h : t.1 ≤ j.1 <;> simp [h]
  rw [h1, ← Finset.sum_coe_sort (Finset.univ.filter (fun t : Fin (k + 1) => t.1 ≤ j.1))]
  let e : Fin (j.1 + 1) ≃ {t : Fin (k + 1) // t ∈ Finset.univ.filter (fun t : Fin (k + 1) => t.1 ≤ j.1)} :=
    ⟨fun i => ⟨⟨i.1, by have := i.2; have := j.2; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; have := i.2; omega⟩⟩,
     fun t => ⟨t.1.1, by have := (Finset.mem_filter.mp t.2).2; omega⟩,
     fun _ => rfl, fun _ => rfl⟩
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

private lemma isSurjFast_iff (k : ℕ) (_hk : 1 ≤ k) (code : Fin (k ^ 4)) :
    isSurjFast k code.1 = true ↔ isSurj k (decYC k code) := by
  unfold isSurjFast isSurj decYC
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h c
    obtain ⟨i, hi, heq⟩ := h c.1 c.2
    exact ⟨⟨i, hi⟩, Fin.ext heq⟩
  · intro h c hc
    obtain ⟨i, hi⟩ := h ⟨c, hc⟩
    exact ⟨i.1, i.2, congrArg Fin.val hi⟩

private lemma dpRun_eq_foldl (N : ℕ) (y : Fin 4 → Fin (N + 1)) (r : ℕ) (hr : r ≤ 4) :
    dpRun N y r hr = ((List.range r).map fun i => if h : i < 4 then (y ⟨i, h⟩).1 else 0).foldl (fun cur yi => dpStep N yi cur) (dpInit N) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    unfold dpRun
    rw [ih (by omega), List.range_succ, List.map_append, List.foldl_append]
    simp [dif_pos (show r < 4 by omega)]

private lemma isValidDP_eq_fast (k : ℕ) (hk : 1 ≤ k) (code : Fin (k ^ 4)) (mask : Fin (2 ^ (k + 1))) :
    isValidDP (NComp k (decCap (k + 1) mask)) (yComp k hk (decYC k code) (decCap (k + 1) mask)) =
    isValidDPFast (k - 1 + popcount (k + 1) mask.1) (yListFast k code.1 mask.1) := by
  unfold isValidDP isValidDPFast
  rw [dpRun_eq_foldl]
  have hN : NComp k (decCap (k + 1) mask) = k - 1 + popcount (k + 1) mask.1 := NComp_decCap_eq k mask
  have hL : ((List.range 4).map fun i => if h : i < 4 then (yComp k hk (decYC k code) (decCap (k + 1) mask) ⟨i, h⟩).1 else 0) =
      yListFast k code.1 mask.1 := by
    unfold yListFast
    apply List.map_congr_left; intro i hi
    rw [List.mem_range] at hi
    rw [dif_pos hi]
    dsimp only [yComp, decYC]
    exact vComp_decCap_eq k mask (decYC k code ⟨i, hi⟩)
  rw [hL, hN]

private lemma sum_fin_eq_foldl_range (n : ℕ) (f : ℕ → ℕ) :
    (∑ i : Fin n, f i.1) = (List.range n).foldl (fun acc i => acc + f i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, List.range_succ, List.foldl_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.foldl_cons, List.foldl_nil, ih]

private lemma wCount_eq_fast (k : Fin 4) (c1 : Fin (k.1 + 3)) :
    (∑ yc : Fin ((k.1 + 1) ^ 4), if isSurj (k.1 + 1) (decYC (k.1 + 1) yc) then ∑ mask : Fin (2 ^ (k.1 + 2)),
      if popcount (k.1 + 2) mask.1 = c1.1 ∧
         isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
           (yComp (k.1 + 1) (by omega) (decYC (k.1 + 1) yc) (decCap (k.1 + 2) mask))
      then 1 else 0 else 0) = wCountFast (k.1 + 1) c1.1 := by
  unfold wCountFast
  let inner (code : ℕ) : ℕ :=
    (List.range (2 ^ (k.1 + 2))).foldl (fun acc2 mask =>
      if popcount (k.1 + 2) mask == c1.1 &&
         isValidDPFast (k.1 + 1 - 1 + popcount (k.1 + 2) mask) (yListFast (k.1 + 1) code mask)
      then acc2 + 1 else acc2) 0
  have h1 : (∑ yc : Fin ((k.1 + 1) ^ 4), if isSurj (k.1 + 1) (decYC (k.1 + 1) yc) then ∑ mask : Fin (2 ^ (k.1 + 2)),
      if popcount (k.1 + 2) mask.1 = c1.1 ∧
         isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
           (yComp (k.1 + 1) (by omega) (decYC (k.1 + 1) yc) (decCap (k.1 + 2) mask))
      then 1 else 0 else 0) =
      ∑ yc : Fin ((k.1 + 1) ^ 4), if isSurjFast (k.1 + 1) yc.1 then inner yc.1 else 0 := by
    apply Finset.sum_congr rfl; intro yc _
    by_cases hs : isSurjFast (k.1 + 1) yc.1 = true
    · have hs' : isSurj (k.1 + 1) (decYC (k.1 + 1) yc) := (isSurjFast_iff (k.1 + 1) (by omega) yc).mp hs
      rw [if_pos hs', if_pos hs]
      have hin : (∑ mask : Fin (2 ^ (k.1 + 2)),
          if popcount (k.1 + 2) mask.1 = c1.1 ∧
             isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
               (yComp (k.1 + 1) (by omega) (decYC (k.1 + 1) yc) (decCap (k.1 + 2) mask))
          then 1 else 0) =
          ∑ mask : Fin (2 ^ (k.1 + 2)),
            (fun m0 => if popcount (k.1 + 2) m0 == c1.1 &&
               isValidDPFast (k.1 + 1 - 1 + popcount (k.1 + 2) m0) (yListFast (k.1 + 1) yc.1 m0)
            then 1 else 0) mask.1 := by
        apply Finset.sum_congr rfl; intro mask _
        rw [isValidDP_eq_fast (k.1 + 1) (by omega) yc mask]
        simp only [Bool.and_eq_true, beq_iff_eq]
      rw [hin, sum_fin_eq_foldl_range (2 ^ (k.1 + 2)) (fun m0 =>
        if popcount (k.1 + 2) m0 == c1.1 &&
           isValidDPFast (k.1 + 1 - 1 + popcount (k.1 + 2) m0) (yListFast (k.1 + 1) yc.1 m0)
        then 1 else 0)]
      dsimp only [inner]; congr 1; funext acc2 mask; split_ifs <;> simp
    · have hs' : ¬isSurj (k.1 + 1) (decYC (k.1 + 1) yc) := (isSurjFast_iff (k.1 + 1) (by omega) yc).not.mp hs
      rw [if_neg hs', if_neg hs]
  rw [h1, sum_fin_eq_foldl_range ((k.1 + 1) ^ 4) (fun code => if isSurjFast (k.1 + 1) code then inner code else 0)]
  congr 1; funext acc code; dsimp only [inner]; split_ifs <;> simp

private lemma wCount_ok_1_0 : wCountFast 1 0 = 0 := by decide
private lemma wCount_ok_1_1 : wCountFast 1 1 = 0 := by decide
private lemma wCount_ok_1_2 : wCountFast 1 2 = 1 := by decide
private lemma wCount_ok_2_0 : wCountFast 2 0 = 2 := by decide
private lemma wCount_ok_2_1 : wCountFast 2 1 = 14 := by decide
private lemma wCount_ok_2_2 : wCountFast 2 2 = 26 := by decide
private lemma wCount_ok_2_3 : wCountFast 2 3 = 14 := by decide
private lemma wCount_ok_3_0_p0 : wCountRange 3 0 0 64 = 14 := by decide
private lemma wCount_ok_3_0_p1 : wCountRange 3 0 64 17 = 2 := by decide
private lemma wCount_ok_3_0 : wCountFast 3 0 = 16 := by
  rw [wCountFast_eq_range, show (3 ^ 4 : ℕ) = 81 from rfl]
  rw [show (81 : ℕ) = 64 + 17 from rfl, wCountRange_add 3 0 0 64 17]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_3_0_p0, wCount_ok_3_0_p1]
private lemma wCount_ok_3_1_p0 : wCountRange 3 1 0 64 = 65 := by decide
private lemma wCount_ok_3_1_p1 : wCountRange 3 1 64 17 = 11 := by decide
private lemma wCount_ok_3_1 : wCountFast 3 1 = 76 := by
  rw [wCountFast_eq_range, show (3 ^ 4 : ℕ) = 81 from rfl]
  rw [show (81 : ℕ) = 64 + 17 from rfl, wCountRange_add 3 1 0 64 17]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_3_1_p0, wCount_ok_3_1_p1]
private lemma wCount_ok_3_2_p0 : wCountRange 3 2 0 64 = 115 := by decide
private lemma wCount_ok_3_2_p1 : wCountRange 3 2 64 17 = 21 := by decide
private lemma wCount_ok_3_2 : wCountFast 3 2 = 136 := by
  rw [wCountFast_eq_range, show (3 ^ 4 : ℕ) = 81 from rfl]
  rw [show (81 : ℕ) = 64 + 17 from rfl, wCountRange_add 3 2 0 64 17]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_3_2_p0, wCount_ok_3_2_p1]
private lemma wCount_ok_3_3_p0 : wCountRange 3 3 0 64 = 91 := by decide
private lemma wCount_ok_3_3_p1 : wCountRange 3 3 64 17 = 17 := by decide
private lemma wCount_ok_3_3 : wCountFast 3 3 = 108 := by
  rw [wCountFast_eq_range, show (3 ^ 4 : ℕ) = 81 from rfl]
  rw [show (81 : ℕ) = 64 + 17 from rfl, wCountRange_add 3 3 0 64 17]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_3_3_p0, wCount_ok_3_3_p1]
private lemma wCount_ok_3_4_p0 : wCountRange 3 4 0 64 = 27 := by decide
private lemma wCount_ok_3_4_p1 : wCountRange 3 4 64 17 = 5 := by decide
private lemma wCount_ok_3_4 : wCountFast 3 4 = 32 := by
  rw [wCountFast_eq_range, show (3 ^ 4 : ℕ) = 81 from rfl]
  rw [show (81 : ℕ) = 64 + 17 from rfl, wCountRange_add 3 4 0 64 17]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_3_4_p0, wCount_ok_3_4_p1]
private lemma wCount_ok_4_0_p0 : wCountRange 4 0 0 64 = 3 := by decide
private lemma wCount_ok_4_0_p1 : wCountRange 4 0 64 64 = 3 := by decide
private lemma wCount_ok_4_0_p2 : wCountRange 4 0 128 64 = 3 := by decide
private lemma wCount_ok_4_0_p3 : wCountRange 4 0 192 64 = 3 := by decide
private lemma wCount_ok_4_0 : wCountFast 4 0 = 12 := by
  rw [wCountFast_eq_range, show (4 ^ 4 : ℕ) = 256 from rfl]
  rw [show (256 : ℕ) = 192 + 64 from rfl, wCountRange_add 4 0 0 192 64]
  rw [show (192 : ℕ) = 128 + 64 from rfl, wCountRange_add 4 0 0 128 64]
  rw [show (128 : ℕ) = 64 + 64 from rfl, wCountRange_add 4 0 0 64 64]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_4_0_p0, wCount_ok_4_0_p1, wCount_ok_4_0_p2, wCount_ok_4_0_p3]
private lemma wCount_ok_4_1_p0 : wCountRange 4 1 0 64 = 16 := by decide
private lemma wCount_ok_4_1_p1 : wCountRange 4 1 64 64 = 16 := by decide
private lemma wCount_ok_4_1_p2 : wCountRange 4 1 128 64 = 16 := by decide
private lemma wCount_ok_4_1_p3 : wCountRange 4 1 192 64 = 16 := by decide
private lemma wCount_ok_4_1 : wCountFast 4 1 = 64 := by
  rw [wCountFast_eq_range, show (4 ^ 4 : ℕ) = 256 from rfl]
  rw [show (256 : ℕ) = 192 + 64 from rfl, wCountRange_add 4 1 0 192 64]
  rw [show (192 : ℕ) = 128 + 64 from rfl, wCountRange_add 4 1 0 128 64]
  rw [show (128 : ℕ) = 64 + 64 from rfl, wCountRange_add 4 1 0 64 64]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_4_1_p0, wCount_ok_4_1_p1, wCount_ok_4_1_p2, wCount_ok_4_1_p3]
private lemma wCount_ok_4_2_p0 : wCountRange 4 2 0 64 = 34 := by decide
private lemma wCount_ok_4_2_p1 : wCountRange 4 2 64 64 = 34 := by decide
private lemma wCount_ok_4_2_p2 : wCountRange 4 2 128 64 = 34 := by decide
private lemma wCount_ok_4_2_p3 : wCountRange 4 2 192 64 = 34 := by decide
private lemma wCount_ok_4_2 : wCountFast 4 2 = 136 := by
  rw [wCountFast_eq_range, show (4 ^ 4 : ℕ) = 256 from rfl]
  rw [show (256 : ℕ) = 192 + 64 from rfl, wCountRange_add 4 2 0 192 64]
  rw [show (192 : ℕ) = 128 + 64 from rfl, wCountRange_add 4 2 0 128 64]
  rw [show (128 : ℕ) = 64 + 64 from rfl, wCountRange_add 4 2 0 64 64]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_4_2_p0, wCount_ok_4_2_p1, wCount_ok_4_2_p2, wCount_ok_4_2_p3]
private lemma wCount_ok_4_3_p0 : wCountRange 4 3 0 64 = 36 := by decide
private lemma wCount_ok_4_3_p1 : wCountRange 4 3 64 64 = 36 := by decide
private lemma wCount_ok_4_3_p2 : wCountRange 4 3 128 64 = 36 := by decide
private lemma wCount_ok_4_3_p3 : wCountRange 4 3 192 64 = 36 := by decide
private lemma wCount_ok_4_3 : wCountFast 4 3 = 144 := by
  rw [wCountFast_eq_range, show (4 ^ 4 : ℕ) = 256 from rfl]
  rw [show (256 : ℕ) = 192 + 64 from rfl, wCountRange_add 4 3 0 192 64]
  rw [show (192 : ℕ) = 128 + 64 from rfl, wCountRange_add 4 3 0 128 64]
  rw [show (128 : ℕ) = 64 + 64 from rfl, wCountRange_add 4 3 0 64 64]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_4_3_p0, wCount_ok_4_3_p1, wCount_ok_4_3_p2, wCount_ok_4_3_p3]
private lemma wCount_ok_4_4_p0 : wCountRange 4 4 0 64 = 19 := by decide
private lemma wCount_ok_4_4_p1 : wCountRange 4 4 64 64 = 19 := by decide
private lemma wCount_ok_4_4_p2 : wCountRange 4 4 128 64 = 19 := by decide
private lemma wCount_ok_4_4_p3 : wCountRange 4 4 192 64 = 19 := by decide
private lemma wCount_ok_4_4 : wCountFast 4 4 = 76 := by
  rw [wCountFast_eq_range, show (4 ^ 4 : ℕ) = 256 from rfl]
  rw [show (256 : ℕ) = 192 + 64 from rfl, wCountRange_add 4 4 0 192 64]
  rw [show (192 : ℕ) = 128 + 64 from rfl, wCountRange_add 4 4 0 128 64]
  rw [show (128 : ℕ) = 64 + 64 from rfl, wCountRange_add 4 4 0 64 64]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_4_4_p0, wCount_ok_4_4_p1, wCount_ok_4_4_p2, wCount_ok_4_4_p3]
private lemma wCount_ok_4_5_p0 : wCountRange 4 5 0 64 = 4 := by decide
private lemma wCount_ok_4_5_p1 : wCountRange 4 5 64 64 = 4 := by decide
private lemma wCount_ok_4_5_p2 : wCountRange 4 5 128 64 = 4 := by decide
private lemma wCount_ok_4_5_p3 : wCountRange 4 5 192 64 = 4 := by decide
private lemma wCount_ok_4_5 : wCountFast 4 5 = 16 := by
  rw [wCountFast_eq_range, show (4 ^ 4 : ℕ) = 256 from rfl]
  rw [show (256 : ℕ) = 192 + 64 from rfl, wCountRange_add 4 5 0 192 64]
  rw [show (192 : ℕ) = 128 + 64 from rfl, wCountRange_add 4 5 0 128 64]
  rw [show (128 : ℕ) = 64 + 64 from rfl, wCountRange_add 4 5 0 64 64]
  simp only [Nat.zero_add, Nat.reduceAdd, wCount_ok_4_5_p0, wCount_ok_4_5_p1, wCount_ok_4_5_p2, wCount_ok_4_5_p3]

private lemma wCount_eq (k : Fin 4) (c1 : Fin (k.1 + 3)) :
    (∑ yc : Fin ((k.1 + 1) ^ 4), if isSurj (k.1 + 1) (decYC (k.1 + 1) yc) then ∑ mask : Fin (2 ^ (k.1 + 2)),
      if popcount (k.1 + 2) mask.1 = c1.1 ∧
         isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
           (yComp (k.1 + 1) (by omega) (decYC (k.1 + 1) yc) (decCap (k.1 + 2) mask))
      then 1 else 0 else 0) = wVal (k.1 + 1) c1.1 := by
  rw [wCount_eq_fast]
  fin_cases k
  · fin_cases c1
    · exact wCount_ok_1_0
    · exact wCount_ok_1_1
    · exact wCount_ok_1_2
  · fin_cases c1
    · exact wCount_ok_2_0
    · exact wCount_ok_2_1
    · exact wCount_ok_2_2
    · exact wCount_ok_2_3
  · fin_cases c1
    · exact wCount_ok_3_0
    · exact wCount_ok_3_1
    · exact wCount_ok_3_2
    · exact wCount_ok_3_3
    · exact wCount_ok_3_4
  · fin_cases c1
    · exact wCount_ok_4_0
    · exact wCount_ok_4_1
    · exact wCount_ok_4_2
    · exact wCount_ok_4_3
    · exact wCount_ok_4_4
    · exact wCount_ok_4_5

private lemma a_eq_weight_sum (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ k : Fin 4, ∑ c1 : Fin (k.1 + 3), wVal (k.1 + 1) c1.1 * gapCard n (k.1 + 1) c1.1 := by
  unfold a; rw [if_neg (by omega)]
  -- Decompose y : Fin m -> Fin (n+1) into (k, yc, cap, v)
  let Φ : (Σ k : Fin 4, Σ yc : {f : Fin 4 → Fin (k.1 + 1) // isSurj (k.1 + 1) f},
      Σ cap : {c : Fin (k.1 + 2) → Bool // isValid (NComp (k.1 + 1) c) (yComp (k.1 + 1) (by omega) yc.1 c)},
      {v : Fin (k.1 + 1) → Fin (n + 1) // StrictMono v ∧ gapsMatch n (k.1 + 1) (by omega) v cap.1}) →
      {y : Fin 4 → Fin (n + 1) // isValid n y} :=
    fun ⟨k, yc, cap, v⟩ =>
      ⟨fun i => v.1 (yc.1 i), (isValid_iff_comp n (k.1 + 1) (by omega) v.1 v.2.1 yc.1 cap.1 v.2.2).mpr cap.2⟩
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨ka, ⟨yca, hsa⟩, ⟨capa, hca⟩, ⟨va, hva, hgma⟩⟩ ⟨kb, ⟨ycb, hsb⟩, ⟨capb, hcb⟩, ⟨vb, hvb, hgmb⟩⟩ heq
      have hfun : (fun i => va (yca i)) = (fun i => vb (ycb i)) := congrArg Subtype.val heq
      have himg : Finset.univ.image (fun i : Fin 4 => va (yca i)) = Finset.univ.image (fun i : Fin 4 => vb (ycb i)) := by rw [hfun]
      have himgA : Finset.univ.image (fun i : Fin 4 => va (yca i)) = Finset.univ.image va := by
        ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩; exact ⟨yca i, rfl⟩
        · rintro ⟨c, rfl⟩; obtain ⟨i, hi⟩ := hsa c; exact ⟨i, by rw [hi]⟩
      have himgB : Finset.univ.image (fun i : Fin 4 => vb (ycb i)) = Finset.univ.image vb := by
        ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩; exact ⟨ycb i, rfl⟩
        · rintro ⟨c, rfl⟩; obtain ⟨i, hi⟩ := hsb c; exact ⟨i, by rw [hi]⟩
      rw [himgA, himgB] at himg
      have hcardA : (Finset.univ.image va).card = ka.1 + 1 := by rw [Finset.card_image_of_injective _ hva.injective, Finset.card_fin]
      have hcardB : (Finset.univ.image vb).card = kb.1 + 1 := by rw [Finset.card_image_of_injective _ hvb.injective, Finset.card_fin]
      have hcard_eq : (Finset.univ.image va).card = (Finset.univ.image vb).card := congrArg Finset.card himg
      have hk : ka = kb := Fin.ext (by omega)
      subst hk
      -- StrictMono with same image => equal!
      have hv_eq : va = vb := by
        let S := Finset.univ.image va
        have hS : S.card = ka.1 + 1 := hcardA
        have hea : ∀ j, va j = (S.orderEmbOfFin hS) j := by
          have := Finset.orderEmbOfFin_unique hS (fun j => by simp [S]) hva
          exact fun j => congrFun this j
        have heb : ∀ j, vb j = (S.orderEmbOfFin hS) j := by
          have := Finset.orderEmbOfFin_unique hS (fun j => by dsimp [S]; rw [himg]; simp) hvb
          exact fun j => congrFun this j
        funext j; rw [hea j, heb j]
      subst hv_eq
      have hyc_eq : yca = ycb := by funext i; exact hva.injective (congrFun hfun i)
      subst hyc_eq
      have hcap_eq : capa = capb := by
        obtain ⟨ha0, ham, hal⟩ := hgma; obtain ⟨hb0, hbm, hbl⟩ := hgmb
        dsimp only at ha0 ham hal hb0 hbm hbl
        funext t
        by_cases ht0 : t.1 = 0
        · have : t = ⟨0, by omega⟩ := Fin.ext ht0; rw [this, ha0, hb0]
        · by_cases htk : t.1 < ka.1 + 1
          · have : t = ⟨(t.1 - 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [this, ham ⟨t.1 - 1, by omega⟩, hbm ⟨t.1 - 1, by omega⟩]
          · have : t = ⟨ka.1 + 1, by omega⟩ := Fin.ext (by have := t.2; dsimp; omega)
            rw [this, hal, hbl]
      subst hcap_eq; rfl
    · rintro ⟨y, hy⟩
      let S := Finset.univ.image y
      have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨y ⟨0, by omega⟩, Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩⟩
      have hS_le : S.card ≤ 4 := by calc S.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
        _ = 4 := Finset.card_fin 4
      let k : Fin 4 := ⟨S.card - 1, by omega⟩
      have hSc : S.card = k.1 + 1 := by dsimp [k]; omega
      let emb := S.orderIsoOfFin hSc
      let v : Fin (k.1 + 1) → Fin (n + 1) := fun j => (emb j).1
      have hv : StrictMono v := fun a b hab => emb.strictMono hab
      let yc : Fin 4 → Fin (k.1 + 1) := fun i => emb.symm ⟨y i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      have hsurj : isSurj (k.1 + 1) yc := by
        intro c
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (emb c).2
        refine ⟨i, ?_⟩; dsimp [yc]
        have : (⟨y i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : S) = emb c := Subtype.ext hi
        rw [this]; exact emb.symm_apply_apply c
      let cap : Fin (k.1 + 2) → Bool := fun t =>
        if h0 : t.1 = 0 then decide (0 < (v ⟨0, by omega⟩).1)
        else if htk : t.1 < k.1 + 1 then decide ((v ⟨t.1 - 1, by omega⟩).1 + 1 < (v ⟨t.1, htk⟩).1)
        else decide ((v ⟨k.1, by omega⟩).1 < n)
      have hgm : gapsMatch n (k.1 + 1) (by omega) v cap := by
        refine ⟨by simp [cap],
                fun j => by dsimp [cap]; rw [dif_pos (by have := j.2; omega)],
                by dsimp [cap]; rw [dif_neg (by omega)]⟩
      have hvyc : (fun i => v (yc i)) = y := by
        funext i; dsimp [v, yc]; exact congrArg Subtype.val (emb.apply_symm_apply _)
      have hyc_val : isValid (NComp (k.1 + 1) cap) (yComp (k.1 + 1) (by omega) yc cap) :=
        (isValid_iff_comp n (k.1 + 1) (by omega) v hv yc cap hgm).mp (by rwa [hvyc])
      exact ⟨⟨k, ⟨yc, hsurj⟩, ⟨cap, hyc_val⟩, ⟨v, hv, hgm⟩⟩, Subtype.ext hvyc⟩
  rw [← Fintype.card_congr (Equiv.ofBijective Φ hbij), Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro k _
  rw [Fintype.card_sigma]
  have hinner : ∀ yc : {f : Fin 4 → Fin (k.1 + 1) // isSurj (k.1 + 1) f},
      Fintype.card (Σ cap : {c : Fin (k.1 + 2) → Bool // isValid (NComp (k.1 + 1) c) (yComp (k.1 + 1) (by omega) yc.1 c)},
        {v : Fin (k.1 + 1) → Fin (n + 1) // StrictMono v ∧ gapsMatch n (k.1 + 1) (by omega) v cap.1}) =
      ∑ mask : Fin (2 ^ (k.1 + 2)),
        if isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
             (yComp (k.1 + 1) (by omega) yc.1 (decCap (k.1 + 2) mask))
        then gapCard n (k.1 + 1) (popcount (k.1 + 2) mask.1) else 0 := by
    intro yc
    rw [Fintype.card_sigma]
    let eCap : {c : Fin (k.1 + 2) → Bool // isValid (NComp (k.1 + 1) c) (yComp (k.1 + 1) (by omega) yc.1 c)} ≃
        {mask : Fin (2 ^ (k.1 + 2)) // isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
          (yComp (k.1 + 1) (by omega) yc.1 (decCap (k.1 + 2) mask)) = true} :=
      ⟨fun ⟨c, hc⟩ => ⟨encCap (k.1 + 2) c, by rw [decCap_encCap, isValidDP_iff]; exact hc⟩,
       fun ⟨mask, hm⟩ => ⟨decCap (k.1 + 2) mask, (isValidDP_iff _ _).mp hm⟩,
       fun ⟨c, _⟩ => Subtype.ext (decCap_encCap _ c),
       fun ⟨mask, _⟩ => Subtype.ext (encCap_decCap _ mask)⟩
    rw [Fintype.sum_equiv eCap _ (fun m' => gapCard n (k.1 + 1) (popcount (k.1 + 2) m'.1.1)) (fun ⟨c, _⟩ => by
      dsimp [eCap]; rw [card_gapsMatch, popcount_eq_card (k.1 + 2) (encCap (k.1 + 2) c), decCap_encCap])]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun mask : Fin (2 ^ (k.1 + 2)) =>
        isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
          (yComp (k.1 + 1) (by omega) yc.1 (decCap (k.1 + 2) mask)) = true)) (by intro x; simp)
        (fun mask => gapCard n (k.1 + 1) (popcount (k.1 + 2) mask.1))]
    rw [Finset.sum_filter]
  simp_rw [hinner]
  let eYC : {f : Fin 4 → Fin (k.1 + 1) // isSurj (k.1 + 1) f} ≃
      {code : Fin ((k.1 + 1) ^ 4) // isSurj (k.1 + 1) (decYC (k.1 + 1) code)} :=
    ⟨fun ⟨f, hf⟩ => ⟨encYC (k.1 + 1) (by omega) f, by rw [decYC_encYC]; exact hf⟩,
     fun ⟨code, hc⟩ => ⟨decYC (k.1 + 1) code, hc⟩,
     fun ⟨f, _⟩ => Subtype.ext (decYC_encYC (k.1 + 1) (by omega) f),
     fun ⟨code, _⟩ => Subtype.ext (encYC_decYC (k.1 + 1) (by omega) code)⟩
  rw [Fintype.sum_equiv eYC _ (fun code => ∑ mask : Fin (2 ^ (k.1 + 2)),
      if isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
           (yComp (k.1 + 1) (by omega) (decYC (k.1 + 1) code.1) (decCap (k.1 + 2) mask))
      then gapCard n (k.1 + 1) (popcount (k.1 + 2) mask.1) else 0)
    (fun ⟨f, _⟩ => by simp only [eYC, Equiv.coe_fn_mk, decYC_encYC])]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun code : Fin ((k.1 + 1) ^ 4) => isSurj (k.1 + 1) (decYC (k.1 + 1) code))) (by intro x; simp)
      (fun code => ∑ mask : Fin (2 ^ (k.1 + 2)),
        if isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
             (yComp (k.1 + 1) (by omega) (decYC (k.1 + 1) code) (decCap (k.1 + 2) mask))
        then gapCard n (k.1 + 1) (popcount (k.1 + 2) mask.1) else 0)]
  rw [Finset.sum_filter]
  -- Group by c1 = popcount (k.1 + 2) mask.1
  have hgroup : (∑ code : Fin ((k.1 + 1) ^ 4),
      if isSurj (k.1 + 1) (decYC (k.1 + 1) code) then
        ∑ mask : Fin (2 ^ (k.1 + 2)),
          if isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
               (yComp (k.1 + 1) (by omega) (decYC (k.1 + 1) code) (decCap (k.1 + 2) mask))
          then gapCard n (k.1 + 1) (popcount (k.1 + 2) mask.1) else 0
      else 0) =
      ∑ c1 : Fin (k.1 + 3),
        (∑ code : Fin ((k.1 + 1) ^ 4), if isSurj (k.1 + 1) (decYC (k.1 + 1) code) then ∑ mask : Fin (2 ^ (k.1 + 2)),
          if popcount (k.1 + 2) mask.1 = c1.1 ∧
             isValidDP (NComp (k.1 + 1) (decCap (k.1 + 2) mask))
               (yComp (k.1 + 1) (by omega) (decYC (k.1 + 1) code) (decCap (k.1 + 2) mask))
          then 1 else 0 else 0) * gapCard n (k.1 + 1) c1.1 := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro code _
    by_cases hs : isSurj (k.1 + 1) (decYC (k.1 + 1) code)
    · simp only [if_pos hs]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro mask _
      have hpc_lt : popcount (k.1 + 2) mask.1 < k.1 + 3 := by
        rw [popcount_eq_card]
        have := Finset.card_le_univ (Finset.univ.filter (fun j : Fin (k.1 + 2) => decCap (k.1 + 2) mask j = true))
        rw [Fintype.card_fin] at this; omega
      rw [Finset.sum_eq_single ⟨popcount (k.1 + 2) mask.1, hpc_lt⟩]
      · simp
      · intro c1 _ hne; have : popcount (k.1 + 2) mask.1 ≠ c1.1 := fun h => hne (Fin.ext h.symm); simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [if_neg hs, zero_mul, Finset.sum_const_zero]
  rw [hgroup]
  apply Finset.sum_congr rfl; intro c1 _
  rw [wCount_eq k c1]

private lemma choose_cast_q_1 (x : ℕ) (hx : 1 ≤ x) :
    (Nat.choose x 1 : ℚ) = (((x : ℚ) - 0)) / 1 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  have hdvd : Nat.factorial 1 ∣ x.descFactorial 1 := Nat.factorial_dvd_descFactorial x 1
  rw [Nat.cast_div (by exact_mod_cast hdvd) (by positivity)]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.cast_mul]
  rw [Nat.cast_sub (show 0 ≤ x by omega)]
  push_cast; ring
private lemma choose_cast_q_2 (x : ℕ) (hx : 2 ≤ x) :
    (Nat.choose x 2 : ℚ) = (((x : ℚ) - 0) * ((x : ℚ) - 1)) / 2 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  have hdvd : Nat.factorial 2 ∣ x.descFactorial 2 := Nat.factorial_dvd_descFactorial x 2
  rw [Nat.cast_div (by exact_mod_cast hdvd) (by positivity)]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.cast_mul]
  rw [Nat.cast_sub (show 0 ≤ x by omega), Nat.cast_sub (show 1 ≤ x by omega)]
  push_cast; ring
private lemma choose_cast_q_3 (x : ℕ) (hx : 3 ≤ x) :
    (Nat.choose x 3 : ℚ) = (((x : ℚ) - 0) * ((x : ℚ) - 1) * ((x : ℚ) - 2)) / 6 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  have hdvd : Nat.factorial 3 ∣ x.descFactorial 3 := Nat.factorial_dvd_descFactorial x 3
  rw [Nat.cast_div (by exact_mod_cast hdvd) (by positivity)]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.cast_mul]
  rw [Nat.cast_sub (show 0 ≤ x by omega), Nat.cast_sub (show 1 ≤ x by omega), Nat.cast_sub (show 2 ≤ x by omega)]
  push_cast; ring
private lemma choose_cast_q_4 (x : ℕ) (hx : 4 ≤ x) :
    (Nat.choose x 4 : ℚ) = (((x : ℚ) - 0) * ((x : ℚ) - 1) * ((x : ℚ) - 2) * ((x : ℚ) - 3)) / 24 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  have hdvd : Nat.factorial 4 ∣ x.descFactorial 4 := Nat.factorial_dvd_descFactorial x 4
  rw [Nat.cast_div (by exact_mod_cast hdvd) (by positivity)]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.cast_mul]
  rw [Nat.cast_sub (show 0 ≤ x by omega), Nat.cast_sub (show 1 ≤ x by omega), Nat.cast_sub (show 2 ≤ x by omega), Nat.cast_sub (show 3 ≤ x by omega)]
  push_cast; ring

private lemma a_poly_q (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 1 * (((n : ℚ) - 1)) / 1 + 14 + 26 * (((n : ℚ) - 2)) / 1 + 14 * (((n : ℚ) - 2) * ((n : ℚ) - 3)) / 2 + 76 + 136 * (((n : ℚ) - 3)) / 1 + 108 * (((n : ℚ) - 3) * ((n : ℚ) - 4)) / 2 + 32 * (((n : ℚ) - 3) * ((n : ℚ) - 4) * ((n : ℚ) - 5)) / 6 + 64 + 136 * (((n : ℚ) - 4)) / 1 + 144 * (((n : ℚ) - 4) * ((n : ℚ) - 5)) / 2 + 76 * (((n : ℚ) - 4) * ((n : ℚ) - 5) * ((n : ℚ) - 6)) / 6 + 16 * (((n : ℚ) - 4) * ((n : ℚ) - 5) * ((n : ℚ) - 6) * ((n : ℚ) - 7)) / 24 := by
  rw [a_eq_weight_sum n (by omega)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, wVal, gapCard]
  simp only [show ¬(n + 1 = 1) by omega, show ¬(n + 1 = 2) by omega, show ¬(n + 1 = 3) by omega, show ¬(n + 1 = 4) by omega,
    show ¬(1 = 0) by omega, show ¬(2 = 0) by omega, show ¬(3 = 0) by omega, show ¬(4 = 0) by omega, show ¬(5 = 0) by omega,
    ↓reduceIte, mul_zero, zero_mul, zero_add]
  simp only [show 3 ≤ n + 1 by omega, show 4 ≤ n + 1 by omega, show 5 ≤ n + 1 by omega, show 6 ≤ n + 1 by omega, show 7 ≤ n + 1 by omega, show 8 ≤ n + 1 by omega, show 9 ≤ n + 1 by omega, ↓reduceIte, Nat.reduceSub]
  push_cast
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one,
    choose_cast_q_1 (n - 1) (by omega), choose_cast_q_1 (n - 2) (by omega), choose_cast_q_2 (n - 2) (by omega), choose_cast_q_1 (n - 3) (by omega), choose_cast_q_2 (n - 3) (by omega), choose_cast_q_3 (n - 3) (by omega), choose_cast_q_1 (n - 4) (by omega), choose_cast_q_2 (n - 4) (by omega), choose_cast_q_3 (n - 4) (by omega), choose_cast_q_4 (n - 4) (by omega)]
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_ofNat]
  ring

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_val_1 : a 1 = 2 := by
  rw [a_eq_weight_sum 1 (by omega)]; decide
private lemma a_val_2 : a 2 = 31 := by
  rw [a_eq_weight_sum 2 (by omega)]; decide
private lemma a_val_3 : a 3 = 130 := by
  rw [a_eq_weight_sum 3 (by omega)]; decide
private lemma a_val_4 : a 4 = 359 := by
  rw [a_eq_weight_sum 4 (by omega)]; decide
private lemma a_val_5 : a 5 = 794 := by
  rw [a_eq_weight_sum 5 (by omega)]; decide
private lemma a_val_6 : a 6 = 1527 := by
  rw [a_eq_weight_sum 6 (by omega)]; decide
private lemma a_val_7 : a 7 = 2666 := by
  rw [a_eq_weight_sum 7 (by omega)]; decide
private lemma a_val_8 : a 8 = 4335 := by
  rw [a_eq_weight_sum 8 (by omega)]; decide
private lemma a_val_9 : a 9 = 6674 := by
  rw [a_eq_weight_sum 9 (by omega)]; decide
private lemma a_val_10 : a 10 = 9839 := by
  rw [a_eq_weight_sum 10 (by omega)]; decide
private lemma a_val_11 : a 11 = 14002 := by
  rw [a_eq_weight_sum 11 (by omega)]; decide
private lemma a_val_12 : a 12 = 19351 := by
  rw [a_eq_weight_sum 12 (by omega)]; decide
private lemma a_val_13 : a 13 = 26090 := by
  rw [a_eq_weight_sum 13 (by omega)]; decide

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ j * f) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      split_ifs with h1 h2
      · simp [Nat.succ_sub_succ]
      · omega
      · omega
      · rfl

private lemma coeff_mul_X_pow_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ j) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  rw [mul_comm]; exact coeff_X_pow_mul_eq f j n

theorem solution : type_of% @OMA.S_oeis_a229014.main := by
  have hrec : ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
    intro n hn
    by_cases hn6 : n = 6
    · subst hn6; simp [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]
    by_cases hn7 : n = 7
    · subst hn7; simp [a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]
    by_cases hn8 : n = 8
    · subst hn8; simp [a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8]
    by_cases hn9 : n = 9
    · subst hn9; simp [a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9]
    by_cases hn10 : n = 10
    · subst hn10; simp [a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10]
    by_cases hn11 : n = 11
    · subst hn11; simp [a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11]
    by_cases hn12 : n = 12
    · subst hn12; simp [a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12]
    by_cases hn13 : n = 13
    · subst hn13; simp [a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13]
    · have ha0 := a_poly_q n (by omega)
      have ha1 : (a (n - 1) : ℚ) = (1 * ((((n : ℚ) - 1) - 1)) / 1 + 14 + 26 * ((((n : ℚ) - 1) - 2)) / 1 + 14 * ((((n : ℚ) - 1) - 2) * (((n : ℚ) - 1) - 3)) / 2 + 76 + 136 * ((((n : ℚ) - 1) - 3)) / 1 + 108 * ((((n : ℚ) - 1) - 3) * (((n : ℚ) - 1) - 4)) / 2 + 32 * ((((n : ℚ) - 1) - 3) * (((n : ℚ) - 1) - 4) * (((n : ℚ) - 1) - 5)) / 6 + 64 + 136 * ((((n : ℚ) - 1) - 4)) / 1 + 144 * ((((n : ℚ) - 1) - 4) * (((n : ℚ) - 1) - 5)) / 2 + 76 * ((((n : ℚ) - 1) - 4) * (((n : ℚ) - 1) - 5) * (((n : ℚ) - 1) - 6)) / 6 + 16 * ((((n : ℚ) - 1) - 4) * (((n : ℚ) - 1) - 5) * (((n : ℚ) - 1) - 6) * (((n : ℚ) - 1) - 7)) / 24) := by
        have h := a_poly_q (n - 1) (by omega); have hsub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
        rw [hsub] at h; exact h
      have ha2 : (a (n - 2) : ℚ) = (1 * ((((n : ℚ) - 2) - 1)) / 1 + 14 + 26 * ((((n : ℚ) - 2) - 2)) / 1 + 14 * ((((n : ℚ) - 2) - 2) * (((n : ℚ) - 2) - 3)) / 2 + 76 + 136 * ((((n : ℚ) - 2) - 3)) / 1 + 108 * ((((n : ℚ) - 2) - 3) * (((n : ℚ) - 2) - 4)) / 2 + 32 * ((((n : ℚ) - 2) - 3) * (((n : ℚ) - 2) - 4) * (((n : ℚ) - 2) - 5)) / 6 + 64 + 136 * ((((n : ℚ) - 2) - 4)) / 1 + 144 * ((((n : ℚ) - 2) - 4) * (((n : ℚ) - 2) - 5)) / 2 + 76 * ((((n : ℚ) - 2) - 4) * (((n : ℚ) - 2) - 5) * (((n : ℚ) - 2) - 6)) / 6 + 16 * ((((n : ℚ) - 2) - 4) * (((n : ℚ) - 2) - 5) * (((n : ℚ) - 2) - 6) * (((n : ℚ) - 2) - 7)) / 24) := by
        have h := a_poly_q (n - 2) (by omega); have hsub : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
        rw [hsub] at h; exact h
      have ha3 : (a (n - 3) : ℚ) = (1 * ((((n : ℚ) - 3) - 1)) / 1 + 14 + 26 * ((((n : ℚ) - 3) - 2)) / 1 + 14 * ((((n : ℚ) - 3) - 2) * (((n : ℚ) - 3) - 3)) / 2 + 76 + 136 * ((((n : ℚ) - 3) - 3)) / 1 + 108 * ((((n : ℚ) - 3) - 3) * (((n : ℚ) - 3) - 4)) / 2 + 32 * ((((n : ℚ) - 3) - 3) * (((n : ℚ) - 3) - 4) * (((n : ℚ) - 3) - 5)) / 6 + 64 + 136 * ((((n : ℚ) - 3) - 4)) / 1 + 144 * ((((n : ℚ) - 3) - 4) * (((n : ℚ) - 3) - 5)) / 2 + 76 * ((((n : ℚ) - 3) - 4) * (((n : ℚ) - 3) - 5) * (((n : ℚ) - 3) - 6)) / 6 + 16 * ((((n : ℚ) - 3) - 4) * (((n : ℚ) - 3) - 5) * (((n : ℚ) - 3) - 6) * (((n : ℚ) - 3) - 7)) / 24) := by
        have h := a_poly_q (n - 3) (by omega); have hsub : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by rw [Nat.cast_sub (by omega)]; norm_num
        rw [hsub] at h; exact h
      have ha4 : (a (n - 4) : ℚ) = (1 * ((((n : ℚ) - 4) - 1)) / 1 + 14 + 26 * ((((n : ℚ) - 4) - 2)) / 1 + 14 * ((((n : ℚ) - 4) - 2) * (((n : ℚ) - 4) - 3)) / 2 + 76 + 136 * ((((n : ℚ) - 4) - 3)) / 1 + 108 * ((((n : ℚ) - 4) - 3) * (((n : ℚ) - 4) - 4)) / 2 + 32 * ((((n : ℚ) - 4) - 3) * (((n : ℚ) - 4) - 4) * (((n : ℚ) - 4) - 5)) / 6 + 64 + 136 * ((((n : ℚ) - 4) - 4)) / 1 + 144 * ((((n : ℚ) - 4) - 4) * (((n : ℚ) - 4) - 5)) / 2 + 76 * ((((n : ℚ) - 4) - 4) * (((n : ℚ) - 4) - 5) * (((n : ℚ) - 4) - 6)) / 6 + 16 * ((((n : ℚ) - 4) - 4) * (((n : ℚ) - 4) - 5) * (((n : ℚ) - 4) - 6) * (((n : ℚ) - 4) - 7)) / 24) := by
        have h := a_poly_q (n - 4) (by omega); have hsub : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by rw [Nat.cast_sub (by omega)]; norm_num
        rw [hsub] at h; exact h
      have ha5 : (a (n - 5) : ℚ) = (1 * ((((n : ℚ) - 5) - 1)) / 1 + 14 + 26 * ((((n : ℚ) - 5) - 2)) / 1 + 14 * ((((n : ℚ) - 5) - 2) * (((n : ℚ) - 5) - 3)) / 2 + 76 + 136 * ((((n : ℚ) - 5) - 3)) / 1 + 108 * ((((n : ℚ) - 5) - 3) * (((n : ℚ) - 5) - 4)) / 2 + 32 * ((((n : ℚ) - 5) - 3) * (((n : ℚ) - 5) - 4) * (((n : ℚ) - 5) - 5)) / 6 + 64 + 136 * ((((n : ℚ) - 5) - 4)) / 1 + 144 * ((((n : ℚ) - 5) - 4) * (((n : ℚ) - 5) - 5)) / 2 + 76 * ((((n : ℚ) - 5) - 4) * (((n : ℚ) - 5) - 5) * (((n : ℚ) - 5) - 6)) / 6 + 16 * ((((n : ℚ) - 5) - 4) * (((n : ℚ) - 5) - 5) * (((n : ℚ) - 5) - 6) * (((n : ℚ) - 5) - 7)) / 24) := by
        have h := a_poly_q (n - 5) (by omega); have hsub : ((n - 5 : ℕ) : ℚ) = (n : ℚ) - 5 := by rw [Nat.cast_sub (by omega)]; norm_num
        rw [hsub] at h; exact h
      have hq : (a n : ℚ) = 5 * (a (n - 1) : ℚ) - 10 * (a (n - 2) : ℚ) + 10 * (a (n - 3) : ℚ) - 5 * (a (n - 4) : ℚ) + (a (n - 5) : ℚ) := by rw [ha0, ha1, ha2, ha3, ha4, ha5]; ring
      exact_mod_cast hq
  refine ⟨?_, hrec⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 5 = 1 - PowerSeries.C 5 * PowerSeries.X ^ 1 + PowerSeries.C 10 * PowerSeries.X ^ 2 - PowerSeries.C 10 * PowerSeries.X ^ 3 + PowerSeries.C 5 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X * (2 - PowerSeries.X) * (1 + 11 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) : PowerSeries ℚ) = PowerSeries.C 2 * PowerSeries.X ^ 1 + PowerSeries.C 21 * PowerSeries.X ^ 2 - PowerSeries.C 5 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  have hX : ∀ (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * PowerSeries.X ^ j) =
      if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro j; rw [coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc, hX,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]; try norm_num
  · simp [a_zero, a_val_1, a_val_2]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; try norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, ↓reduceIte,
      show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show ¬(m + 6 = 1) by omega, show ¬(m + 6 = 2) by omega, show ¬(m + 6 = 3) by omega, show ¬(m + 6 = 4) by omega, show ¬(m + 6 = 5) by omega]
    have hr := hrec (m + 6) (by omega)
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega] at hr
    have hrq : (a (m + 6) : ℚ) = 5 * (a (m + 5) : ℚ) - 10 * (a (m + 4) : ℚ) + 10 * (a (m + 3) : ℚ) - 5 * (a (m + 2) : ℚ) + (a (m + 1) : ℚ) := by exact_mod_cast hr
    linarith

end OMA.P_oeis_a229014

theorem OMA.solution : type_of% @OMA.S_oeis_a229014.main :=
  OMA.P_oeis_a229014.solution
