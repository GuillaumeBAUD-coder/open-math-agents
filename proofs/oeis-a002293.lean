import OMAStatements.S_oeis_a002293

-- Problem: OEIS A002293 — Three copies of each letter, avoiding 231 and 221
-- Upstream: statements/oeis-a002293.lean (declaration OMA.S_oeis_a002293.main)
-- Credit: @jared-jasinski (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a002293

open OMA.S_oeis_a002293

/-! ### Part 1: 3-Dyck paths and Raney's Cycle Lemma -/

lemma bool_list_length (l : List Bool) : l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [ih] <;> omega

def Is3Dyck (n : ℕ) (p : List Bool) : Prop :=
  p.length = 4 * n ∧ p.count true = n ∧
  ∀ k ≤ p.length, (p.take k).count false ≤ 3 * (p.take k).count true

def weight (n : ℕ) (S : Finset (Fin (4 * n + 1))) (k : ℕ) : ℤ :=
  4 * ((S.filter (fun i => i.val < k)).card : ℤ) - (k : ℤ)

def ValidSet (n : ℕ) : Type :=
  {S : Finset (Fin (4 * n + 1)) // S.card = n ∧ ∀ k ≤ 4 * n, 0 ≤ weight n S k}

def rot (n : ℕ) (r : Fin (4 * n + 1)) (S : Finset (Fin (4 * n + 1))) :
    Finset (Fin (4 * n + 1)) :=
  S.image (· - r)

lemma rot_card (n : ℕ) (r : Fin (4 * n + 1)) (S : Finset (Fin (4 * n + 1))) :
    (rot n r S).card = S.card := by
  unfold rot
  exact Finset.card_image_of_injective S (fun _ _ h => sub_left_inj.mp h)

lemma rot_zero (n : ℕ) (S : Finset (Fin (4 * n + 1))) : rot n 0 S = S := by
  ext x; simp [rot]

lemma rot_add (n : ℕ) (r₁ r₂ : Fin (4 * n + 1)) (S : Finset (Fin (4 * n + 1))) :
    rot n r₁ (rot n r₂ S) = rot n (r₁ + r₂) S := by
  ext x
  simp only [rot, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by abel⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z - r₂, ⟨z, hz, rfl⟩, by abel⟩

lemma fin_sub_val_lt {N : ℕ} [NeZero N] (i r : Fin N) (j : ℕ) (hj : j ≤ N) :
    (i - r).val < j ↔
      (if r.val + j ≤ N then r.val ≤ i.val ∧ i.val < r.val + j
       else r.val ≤ i.val ∨ i.val < r.val + j - N) := by
  have hi := i.isLt
  have hr := r.isLt
  have hsub : (i - r).val = if r.val ≤ i.val then i.val - r.val else i.val + N - r.val := by
    rw [Fin.sub_def]
    split_ifs with h
    · have : (N - r.val + i.val) % N = i.val - r.val := by
        have h1 : N - r.val + i.val = (i.val - r.val) + N := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      exact this
    · have : (N - r.val + i.val) % N = i.val + N - r.val := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      exact this
  rw [hsub]
  split_ifs <;> omega

lemma weight_rot (n : ℕ) (S : Finset (Fin (4 * n + 1))) (hS : S.card = n)
    (r : Fin (4 * n + 1)) (j : ℕ) (hj : j ≤ 4 * n + 1) :
    weight n (rot n r S) j =
      if r.val + j ≤ 4 * n + 1 then
        weight n S (r.val + j) - weight n S r.val
      else
        weight n S (r.val + j - (4 * n + 1)) - weight n S r.val - 1 := by
  have hcard_img :
      ((rot n r S).filter (fun i => i.val < j)).card =
      (S.filter (fun i => (i - r).val < j)).card := by
    unfold rot
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ (fun _ _ h => sub_left_inj.mp h)
  unfold weight
  rw [hcard_img]
  split_ifs with hle
  · have hpart : (S.filter (fun i => i.val < r.val + j)).card =
        (S.filter (fun i => i.val < r.val)).card +
        (S.filter (fun i => (i - r).val < j)).card := by
      have hunion : S.filter (fun i => i.val < r.val + j) =
          S.filter (fun i => i.val < r.val) ∪ S.filter (fun i => (i - r).val < j) := by
        ext i
        simp only [Finset.mem_union, Finset.mem_filter]
        rw [fin_sub_val_lt i r j hj, if_pos hle]
        constructor
        · intro ⟨hiS, hlt⟩
          by_cases h : i.val < r.val
          · exact Or.inl ⟨hiS, h⟩
          · exact Or.inr ⟨hiS, by omega, hlt⟩
        · rintro (⟨hiS, hlt⟩ | ⟨hiS, _, hlt⟩)
          · exact ⟨hiS, by omega⟩
          · exact ⟨hiS, hlt⟩
      have hdisj : Disjoint (S.filter (fun i => i.val < r.val))
          (S.filter (fun i => (i - r).val < j)) := by
        rw [Finset.disjoint_left]
        intro i h1 h2
        simp only [Finset.mem_filter] at h1 h2
        rw [fin_sub_val_lt i r j hj, if_pos hle] at h2
        omega
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hpartZ : ((S.filter (fun i => i.val < r.val + j)).card : ℤ) =
        ((S.filter (fun i => i.val < r.val)).card : ℤ) +
        ((S.filter (fun i => (i - r).val < j)).card : ℤ) := by exact_mod_cast hpart
    push_cast
    linarith
  · have hpart : (S.filter (fun i => (i - r).val < j)).card +
        (S.filter (fun i => i.val < r.val)).card =
        S.card + (S.filter (fun i => i.val < r.val + j - (4 * n + 1))).card := by
      have h1 : S.filter (fun i => (i - r).val < j) =
          S.filter (fun i => r.val ≤ i.val) ∪
          S.filter (fun i => i.val < r.val + j - (4 * n + 1)) := by
        ext i
        simp only [Finset.mem_union, Finset.mem_filter]
        rw [fin_sub_val_lt i r j hj, if_neg hle]
        tauto
      have hdisj1 : Disjoint (S.filter (fun i => r.val ≤ i.val))
          (S.filter (fun i => i.val < r.val + j - (4 * n + 1))) := by
        rw [Finset.disjoint_left]
        intro i h1 h2
        simp only [Finset.mem_filter] at h1 h2
        omega
      have hcomp : (S.filter (fun i => r.val ≤ i.val)).card +
          (S.filter (fun i => i.val < r.val)).card = S.card := by
        have hu : S.filter (fun i => r.val ≤ i.val) ∪ S.filter (fun i => i.val < r.val) = S := by
          ext i; simp only [Finset.mem_union, Finset.mem_filter]; constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h; by_cases hr : r.val ≤ i.val <;> [exact Or.inl ⟨h, hr⟩; exact Or.inr ⟨h, by omega⟩]
        have hd : Disjoint (S.filter (fun i => r.val ≤ i.val)) (S.filter (fun i => i.val < r.val)) := by
          rw [Finset.disjoint_left]; intro i ha hb; simp only [Finset.mem_filter] at ha hb; omega
        rw [← Finset.card_union_of_disjoint hd, hu]
      rw [h1, Finset.card_union_of_disjoint hdisj1]
      omega
    have hpartZ : ((S.filter (fun i => (i - r).val < j)).card : ℤ) +
        ((S.filter (fun i => i.val < r.val)).card : ℤ) =
        (n : ℤ) + ((S.filter (fun i => i.val < r.val + j - (4 * n + 1))).card : ℤ) := by
      rw [hS] at hpart; exact_mod_cast hpart
    have hsubZ : ((r.val + j - (4 * n + 1) : ℕ) : ℤ) =
        (r.val : ℤ) + (j : ℤ) - (4 * (n : ℤ) + 1) := by
      have : 4 * n + 1 ≤ r.val + j := by omega
      rw [Nat.cast_sub this]; push_cast; ring
    rw [hsubZ]
    linarith

lemma rot_valid_iff (n : ℕ) (S : Finset (Fin (4 * n + 1))) (hS : S.card = n)
    (r : Fin (4 * n + 1)) :
    (∀ j ≤ 4 * n, 0 ≤ weight n (rot n r S) j) ↔
      (∀ m ≤ 4 * n, r.val ≤ m → weight n S r.val ≤ weight n S m) ∧
      (∀ m < r.val, weight n S r.val < weight n S m) := by
  constructor
  · intro h
    constructor
    · intro m hm hrm
      have hj : m - r.val ≤ 4 * n := by omega
      have h0 := h (m - r.val) hj
      rw [weight_rot n S hS r (m - r.val) (by omega), if_pos (by omega)] at h0
      have heq : r.val + (m - r.val) = m := by omega
      rw [heq] at h0
      linarith
    · intro m hmr
      by_cases hm0 : m = 0
      · subst hm0
        have hj : 4 * n + 1 - r.val ≤ 4 * n := by omega
        have h0 := h (4 * n + 1 - r.val) hj
        rw [weight_rot n S hS r (4 * n + 1 - r.val) (by omega), if_pos (by omega)] at h0
        have heq : r.val + (4 * n + 1 - r.val) = 4 * n + 1 := by omega
        have hw0 : weight n S 0 = 0 := by simp [weight]
        have hwN : weight n S (4 * n + 1) = -1 := by
          unfold weight
          have : S.filter (fun i : Fin (4 * n + 1) => i.val < 4 * n + 1) = S := by
            ext i; simp only [Finset.mem_filter, and_iff_left_iff_imp]; intro _; exact i.isLt
          rw [this, hS]; push_cast; ring
        rw [heq, hwN] at h0
        rw [hw0]
        linarith
      · have hj : m + (4 * n + 1) - r.val ≤ 4 * n := by omega
        have h0 := h (m + (4 * n + 1) - r.val) hj
        rw [weight_rot n S hS r (m + (4 * n + 1) - r.val) (by omega), if_neg (by omega)] at h0
        have heq : r.val + (m + (4 * n + 1) - r.val) - (4 * n + 1) = m := by omega
        rw [heq] at h0
        linarith
  · rintro ⟨hge, hlt⟩ j hj
    rw [weight_rot n S hS r j (by omega)]
    split_ifs with hle
    · have h1 : r.val + j ≤ 4 * n ∨ r.val + j = 4 * n + 1 := by omega
      rcases h1 with hle' | heq
      · linarith [hge (r.val + j) hle' (by omega)]
      · have hrpos : 0 < r.val := by omega
        have hlt0 := hlt 0 hrpos
        have hw0 : weight n S 0 = 0 := by simp [weight]
        have hwN : weight n S (4 * n + 1) = -1 := by
          unfold weight
          have : S.filter (fun i : Fin (4 * n + 1) => i.val < 4 * n + 1) = S := by
            ext i; simp only [Finset.mem_filter, and_iff_left_iff_imp]; intro _; exact i.isLt
          rw [this, hS]; push_cast; ring
        rw [heq, hwN]
        linarith
    · have hltm := hlt (r.val + j - (4 * n + 1)) (by omega)
      linarith

lemma existsUnique_valid_rot (n : ℕ) (S : Finset (Fin (4 * n + 1))) (hS : S.card = n) :
    ∃! r : Fin (4 * n + 1), ∀ j ≤ 4 * n, 0 ≤ weight n (rot n r S) j := by
  have hne : (Finset.univ : Finset (Fin (4 * n + 1))).Nonempty := ⟨0, Finset.mem_univ _⟩
  let vals := (Finset.univ : Finset (Fin (4 * n + 1))).image (fun r => weight n S r.val)
  let minW := vals.min' (hne.image _)
  let mins := (Finset.univ : Finset (Fin (4 * n + 1))).filter (fun r => weight n S r.val = minW)
  have hmins_ne : mins.Nonempty := by
    have hmem : minW ∈ vals := Finset.min'_mem vals (hne.image _)
    rw [Finset.mem_image] at hmem
    obtain ⟨r, _, hr⟩ := hmem
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩⟩
  let r0 := mins.min' hmins_ne
  have hr0_mem : r0 ∈ mins := Finset.min'_mem mins hmins_ne
  have hr0_eq : weight n S r0.val = minW := (Finset.mem_filter.mp hr0_mem).2
  have hr0_valid : ∀ j ≤ 4 * n, 0 ≤ weight n (rot n r0 S) j := by
    rw [rot_valid_iff n S hS r0]
    constructor
    · intro m hm _
      rw [hr0_eq]
      exact Finset.min'_le vals (weight n S m)
        (Finset.mem_image.mpr ⟨⟨m, by omega⟩, Finset.mem_univ _, rfl⟩)
    · intro m hmr
      have hle : minW ≤ weight n S m := Finset.min'_le vals (weight n S m)
        (Finset.mem_image.mpr ⟨⟨m, by omega⟩, Finset.mem_univ _, rfl⟩)
      by_contra hnot
      have heq : weight n S m = minW := by linarith
      have hm_mem : (⟨m, by omega⟩ : Fin (4 * n + 1)) ∈ mins :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
      have hr0_le := Finset.min'_le mins ⟨m, by omega⟩ hm_mem
      have : r0.val ≤ m := hr0_le
      omega
  refine ⟨r0, hr0_valid, ?_⟩
  intro r hr
  rw [rot_valid_iff n S hS r] at hr
  rw [rot_valid_iff n S hS r0] at hr0_valid
  by_contra hne_r
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne_r) with hlt | hgt
  · have h1 := hr.1 r0.val (by omega) (le_of_lt hlt)
    have h2 := hr0_valid.2 r.val hlt
    linarith
  · have h1 := hr0_valid.1 r.val (by omega) (le_of_lt hgt)
    have h2 := hr.2 r0.val hgt
    linarith

lemma card_validSet (n : ℕ) :
    Nat.card (ValidSet n) = Nat.choose (4 * n) n / (3 * n + 1) := by
  classical
  let T := {S : Finset (Fin (4 * n + 1)) // S.card = n}
  let findR : T → Fin (4 * n + 1) := fun S => (existsUnique_valid_rot n S.1 S.2).choose
  have hfindR : ∀ S : T, ∀ j ≤ 4 * n, 0 ≤ weight n (rot n (findR S) S.1) j :=
    fun S => (existsUnique_valid_rot n S.1 S.2).choose_spec.1
  have hfindR_uniq : ∀ (S : T) (r : Fin (4 * n + 1)),
      (∀ j ≤ 4 * n, 0 ≤ weight n (rot n r S.1) j) → r = findR S :=
    fun S r hr => (existsUnique_valid_rot n S.1 S.2).choose_spec.2 r hr
  let e : ValidSet n × Fin (4 * n + 1) ≃ T := {
    toFun := fun ⟨S, r⟩ => ⟨rot n (-r) S.1, by rw [rot_card]; exact S.2.1⟩
    invFun := fun S => (⟨rot n (findR S) S.1, by rw [rot_card]; exact S.2, hfindR S⟩, findR S)
    left_inv := by
      rintro ⟨⟨S, hScard, hSval⟩, r⟩
      have hrot_eq : rot n r (rot n (-r) S) = S := by
        rw [rot_add, add_neg_cancel, rot_zero]
      have hr_eq : r = findR ⟨rot n (-r) S, by rw [rot_card]; exact hScard⟩ := by
        apply hfindR_uniq
        rw [hrot_eq]
        exact hSval
      ext1
      · apply Subtype.ext
        dsimp
        rw [← hr_eq, hrot_eq]
      · exact hr_eq.symm
    right_inv := by
      intro S
      apply Subtype.ext
      dsimp
      rw [rot_add, neg_add_cancel, rot_zero]
  }
  have hcard_e : Nat.card (ValidSet n) * (4 * n + 1) = Nat.card T := by
    have := Nat.card_congr e
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (4 * n + 1)), Fintype.card_fin] at this
    exact this
  have hcard_T : Nat.card T = (4 * n + 1).choose n := by
    have hbij : T ≃ ↥(Finset.powersetCard n (Finset.univ : Finset (Fin (4 * n + 1)))) := {
      toFun := fun ⟨S, hS⟩ => ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS⟩⟩
      invFun := fun ⟨S, hS⟩ => ⟨S, (Finset.mem_powersetCard.mp hS).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
    rw [Nat.card_congr hbij, Nat.card_eq_fintype_card, Fintype.card_coe,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hcard_T] at hcard_e
  have hbinom : (3 * n + 1) * (4 * n + 1).choose n = (4 * n + 1) * (4 * n).choose n := by
    have hs1 : (4 * n + 1).choose n = (4 * n + 1).choose (3 * n + 1) := by
      rw [← Nat.choose_symm (by omega : n ≤ 4 * n + 1)]
      congr 1; omega
    have hs2 : (4 * n).choose n = (4 * n).choose (3 * n) := by
      rw [← Nat.choose_symm (by omega : n ≤ 4 * n)]
      congr 1; omega
    rw [hs1, hs2, Nat.choose_succ_succ (4 * n) (3 * n)]
    have h1 := Nat.choose_succ_right_eq (4 * n) (3 * n)
    have hsub : 4 * n - 3 * n = n := by omega
    rw [hsub] at h1
    nlinarith
  have hmul : Nat.card (ValidSet n) * (3 * n + 1) = (4 * n).choose n := by
    have h1 : (Nat.card (ValidSet n) * (3 * n + 1)) * (4 * n + 1) =
        (4 * n).choose n * (4 * n + 1) := by
      calc (Nat.card (ValidSet n) * (3 * n + 1)) * (4 * n + 1)
          = (3 * n + 1) * (Nat.card (ValidSet n) * (4 * n + 1)) := by ring
        _ = (3 * n + 1) * (4 * n + 1).choose n := by rw [hcard_e]
        _ = (4 * n + 1) * (4 * n).choose n := hbinom
        _ = (4 * n).choose n * (4 * n + 1) := by ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) h1
  rw [← hmul, Nat.mul_div_cancel _ (by omega)]

def dyckToSet (n : ℕ) (p : List Bool) : Finset (Fin (4 * n + 1)) :=
  Finset.univ.filter (fun i => p.getD i.val false = true)

def setToDyck (n : ℕ) (S : Finset (Fin (4 * n + 1))) : List Bool :=
  List.ofFn (fun i : Fin (4 * n) => decide ((⟨i.val, by omega⟩ : Fin (4 * n + 1)) ∈ S))

lemma card_dyckToSet_filter (n : ℕ) (p : List Bool) (hlen : p.length = 4 * n) :
    ∀ k ≤ 4 * n, ((dyckToSet n p).filter (fun i => i.val < k)).card = (p.take k).count true := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ 4 * n := by omega
    have htake : p.take (k + 1) = p.take k ++ [p[k]'(by omega)] :=
      List.take_succ_eq_append_getElem (by omega)
    rw [htake, List.count_append, List.count_singleton]
    have hgetk : p.getD k false = p[k]'(by omega) := List.getD_eq_getElem _ _ (by omega)
    by_cases hp : p[k]'(by omega) = true
    · have hfilt : (dyckToSet n p).filter (fun i => i.val < k + 1) =
          (dyckToSet n p).filter (fun i => i.val < k) ∪ {⟨k, by omega⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, dyckToSet,
          Finset.mem_univ, true_and, Fin.ext_iff]
        constructor
        · intro ⟨hi, hlt⟩
          by_cases hik : i.val < k
          · exact Or.inl ⟨hi, hik⟩
          · exact Or.inr (show i.val = k by omega)
        · rintro (⟨hi, hlt⟩ | heq)
          · exact ⟨hi, by omega⟩
          · refine ⟨?_, by omega⟩
            change i.val = k at heq
            rw [heq, hgetk]; exact hp
      have hdisj : Disjoint ((dyckToSet n p).filter (fun i => i.val < k)) {⟨k, by omega⟩} := by
        rw [Finset.disjoint_singleton_right]; simp
      rw [hfilt, Finset.card_union_of_disjoint hdisj, Finset.card_singleton, ih hk', hp]
      simp
    · have hfilt : (dyckToSet n p).filter (fun i => i.val < k + 1) =
          (dyckToSet n p).filter (fun i => i.val < k) := by
        ext i
        simp only [Finset.mem_filter, dyckToSet, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hi, hlt⟩
          refine ⟨hi, ?_⟩
          by_contra hge
          have heq : i.val = k := by omega
          rw [heq, hgetk] at hi
          exact hp hi
        · intro ⟨hi, hlt⟩; exact ⟨hi, by omega⟩
      have hbf : p[k]'(by omega) = false := by cases h : p[k]'(by omega) <;> simp_all
      rw [hfilt, ih hk', hbf]
      simp

lemma card_setToDyck_take (n : ℕ) (S : Finset (Fin (4 * n + 1))) :
    ∀ k ≤ 4 * n, ((setToDyck n S).take k).count true = (S.filter (fun i => i.val < k)).card := by
  intro k hk
  have hlen : (setToDyck n S).length = 4 * n := List.length_ofFn
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ 4 * n := by omega
    have htake : (setToDyck n S).take (k + 1) = (setToDyck n S).take k ++ [(setToDyck n S)[k]'(by omega)] :=
      List.take_succ_eq_append_getElem (by omega)
    rw [htake, List.count_append, List.count_singleton]
    have hpk : (setToDyck n S)[k]'(by omega) = decide ((⟨k, by omega⟩ : Fin (4 * n + 1)) ∈ S) := by
      simp [setToDyck]
    rw [hpk]
    by_cases hm : (⟨k, by omega⟩ : Fin (4 * n + 1)) ∈ S
    · have hfilt : S.filter (fun i => i.val < k + 1) =
          S.filter (fun i => i.val < k) ∪ {⟨k, by omega⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
        constructor
        · intro ⟨hiS, hlt⟩
          by_cases hik : i.val < k
          · exact Or.inl ⟨hiS, hik⟩
          · exact Or.inr (Fin.ext (show i.val = k by omega))
        · rintro (⟨hiS, hlt⟩ | rfl)
          · exact ⟨hiS, by omega⟩
          · exact ⟨hm, show k < k + 1 by omega⟩
      have hdisj : Disjoint (S.filter (fun i => i.val < k)) {⟨k, by omega⟩} := by
        rw [Finset.disjoint_singleton_right]; simp
      rw [hfilt, Finset.card_union_of_disjoint hdisj, Finset.card_singleton, ih hk']
      simp [hm]
    · have hfilt : S.filter (fun i => i.val < k + 1) = S.filter (fun i => i.val < k) := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · intro ⟨hiS, hlt⟩
          refine ⟨hiS, ?_⟩
          by_contra hge
          have heq : i = ⟨k, by omega⟩ := Fin.ext (show i.val = k by omega)
          exact hm (heq ▸ hiS)
        · intro ⟨hiS, hlt⟩; exact ⟨hiS, by omega⟩
      rw [hfilt, ih hk']
      simp [hm]

lemma validSet_notMem_last (n : ℕ) (S : Finset (Fin (4 * n + 1))) (hScard : S.card = n)
    (hSval : ∀ k ≤ 4 * n, 0 ≤ weight n S k) :
    (⟨4 * n, by omega⟩ : Fin (4 * n + 1)) ∉ S := by
  intro hmem
  have hw4n := hSval (4 * n) le_rfl
  unfold weight at hw4n
  have hlt : (S.filter (fun i => i.val < 4 * n)).card < S.card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hlt4 := (Finset.mem_filter.mp (heq ▸ hmem)).2
    change 4 * n < 4 * n at hlt4
    omega
  omega

def dyckEquivValidSet (n : ℕ) : {p : List Bool // Is3Dyck n p} ≃ ValidSet n where
  toFun := fun ⟨p, hlen, hcnt, hpre⟩ =>
    ⟨dyckToSet n p, by
      constructor
      · have hSall : dyckToSet n p = (dyckToSet n p).filter (fun i => i.val < 4 * n) := by
          ext i
          simp only [Finset.mem_filter, dyckToSet, Finset.mem_univ, true_and]
          constructor
          · intro h
            refine ⟨h, ?_⟩
            by_contra hge
            have hget : p.getD i.val false = false := List.getD_eq_default _ _ (by omega)
            rw [hget] at h; exact Bool.false_ne_true h
          · exact And.left
        rw [hSall, card_dyckToSet_filter n p hlen (4 * n) le_rfl, ← hlen, List.take_length]
        exact hcnt
      · intro k hk
        unfold weight
        rw [card_dyckToSet_filter n p hlen k hk]
        have hlen_take : (p.take k).length = k := by rw [List.length_take]; omega
        have hsum := bool_list_length (p.take k)
        have hp' := hpre k (by omega)
        omega⟩
  invFun := fun ⟨S, hScard, hSval⟩ =>
    ⟨setToDyck n S, by
      have hlen : (setToDyck n S).length = 4 * n := List.length_ofFn
      have hlast := validSet_notMem_last n S hScard hSval
      refine ⟨hlen, ?_, ?_⟩
      · have h1 : (setToDyck n S).take (4 * n) = setToDyck n S := by rw [← hlen, List.take_length]
        rw [← h1, card_setToDyck_take n S (4 * n) le_rfl]
        have hfilt : S.filter (fun i => i.val < 4 * n) = S := by
          ext i; simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro hi
          by_contra hge
          have heq : i = ⟨4 * n, by omega⟩ := Fin.ext (show i.val = 4 * n by omega)
          exact hlast (heq ▸ hi)
        rw [hfilt, hScard]
      · intro k hk
        rw [hlen] at hk
        have hlen_take : ((setToDyck n S).take k).length = k := by rw [List.length_take]; omega
        have hsum := bool_list_length ((setToDyck n S).take k)
        have hw := hSval k hk
        unfold weight at hw
        rw [← card_setToDyck_take n S k hk] at hw
        omega⟩
  left_inv := by
    rintro ⟨p, hlen, _, _⟩
    apply Subtype.ext
    apply List.ext_getElem
    · simp [setToDyck, hlen]
    · intro i h1 h2
      simp only [setToDyck, List.getElem_ofFn, dyckToSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hget : p.getD i false = p[i]'(by omega) := List.getD_eq_getElem _ _ (by omega)
      rw [hget]
      cases p[i] <;> simp
  right_inv := by
    rintro ⟨S, hScard, hSval⟩
    apply Subtype.ext
    ext i
    simp only [dyckToSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i.val < 4 * n
    · have hlen : (setToDyck n S).length = 4 * n := List.length_ofFn
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp [setToDyck, Fin.eta]
    · have hlen : (setToDyck n S).length = 4 * n := List.length_ofFn
      rw [List.getD_eq_default _ _ (by omega)]
      simp only [Bool.false_eq_true, false_iff]
      intro hmem
      have heq : i = ⟨4 * n, by omega⟩ := Fin.ext (show i.val = 4 * n by omega)
      exact validSet_notMem_last n S hScard hSval (heq ▸ hmem)

lemma card_is3Dyck (n : ℕ) :
    Nat.card {p : List Bool // Is3Dyck n p} = Nat.choose (4 * n) n / (3 * n + 1) := by
  rw [Nat.card_congr (dyckEquivValidSet n), card_validSet]

/-! ### Part 2: Stack-sorting bijection between UniformAvoidingList and Is3Dyck -/

def IsUniformAvoidingList (n : ℕ) (w : List (Fin n)) : Prop :=
  (∀ c : Fin n, w.count c = 3) ∧
  ∀ i j k (hi : i < w.length) (hj : j < w.length) (hk : k < w.length),
    i < j → j < k → ¬ (w[k] < w[i] ∧ w[i] ≤ w[j])

lemma sum_count_eq_length {n : ℕ} (w : List (Fin n)) : ∑ c : Fin n, w.count c = w.length := by
  induction w with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib, ih]
    have : (∑ c : Fin n, if a == c then 1 else 0) = 1 := by
      simp [beq_iff_eq]
    omega

lemma length_of_count_three {n : ℕ} (w : List (Fin n)) (hc : ∀ c : Fin n, w.count c = 3) :
    w.length = 3 * n := by
  have hsum := sum_count_eq_length w
  have hsum3 : ∑ c : Fin n, w.count c = 3 * n := by
    simp [hc, mul_comm]
  omega

lemma count_ofFn {α : Type*} [DecidableEq α] {m : ℕ} (f : Fin m → α) (c : α) :
    (List.ofFn f).count c = (Finset.univ.filter fun i : Fin m => f i = c).card := by
  rw [Finset.card_filter]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.sum_univ_succ]
    by_cases h : f 0 = c <;> simp [h, beq_iff_eq] <;> omega

def wordEquivList (n : ℕ) :
    {word : Fin (3 * n) → Fin n // IsUniformAvoidingWord word} ≃
    {w : List (Fin n) // IsUniformAvoidingList n w} where
  toFun := fun ⟨word, hcnt, hav⟩ =>
    ⟨List.ofFn word, by
      constructor
      · intro c
        rw [count_ofFn]; exact hcnt c
      · intro i j k hi hj hk hij hjk
        simp only [List.length_ofFn] at hi hj hk
        simp only [List.getElem_ofFn]
        exact hav ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk⟩
  invFun := fun ⟨w, hcnt, hav⟩ =>
    have hlen : w.length = 3 * n := length_of_count_three w hcnt
    ⟨fun i => w[i.val]'(by omega), by
      constructor
      · intro c
        have h1 : (Finset.univ.filter fun i : Fin (3 * n) => w[i.val]'(by omega) = c).card = w.count c := by
          have hw : w = List.ofFn (fun i : Fin (3 * n) => w[i.val]'(by omega)) := by
            apply List.ext_getElem (by simp [hlen])
            intro i h1 h2; simp
          conv_rhs => rw [hw]
          exact (count_ofFn _ c).symm
        rw [h1]; exact hcnt c
      · intro i j k hij hjk
        exact hav i.val j.val k.val (by omega) (by omega) (by omega) hij hjk⟩
  left_inv := by
    rintro ⟨word, _, _⟩
    apply Subtype.ext; funext i; simp
  right_inv := by
    rintro ⟨w, hcnt, _⟩
    have hlen := length_of_count_three w hcnt
    apply Subtype.ext
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2; simp

def sorted3Prefix (n k : ℕ) (hk : k ≤ 3 * n) : List (Fin n) :=
  List.ofFn (fun i : Fin k => ⟨i.val / 3, by omega⟩)

lemma sorted3Prefix_succ (n k : ℕ) (hk : k + 1 ≤ 3 * n) :
    sorted3Prefix n (k + 1) hk = sorted3Prefix n k (by omega) ++ [⟨k / 3, by omega⟩] := by
  apply List.ext_getElem
  · simp [sorted3Prefix]
  · intro i h1 h2
    simp only [sorted3Prefix, List.length_ofFn] at h1
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp [sorted3Prefix]; exact hik)]
      simp only [sorted3Prefix, List.getElem_ofFn]
    · have heq : i = k := by omega
      rw [List.getElem_append_right (by simp [sorted3Prefix]; omega)]
      simp only [sorted3Prefix, List.getElem_ofFn, List.length_ofFn, heq, Nat.sub_self,
        List.getElem_singleton]

lemma sorted3Prefix_mem_lt {n k : ℕ} {hk : k ≤ 3 * n} {y : Fin n}
    (hy : y ∈ sorted3Prefix n k hk) : 3 * y.val < k := by
  rw [sorted3Prefix, List.mem_ofFn] at hy
  obtain ⟨i, rfl⟩ := hy
  have := i.isLt
  change 3 * (i.val / 3) < k
  omega

lemma sorted3Prefix_count (n : ℕ) (c : Fin n) :
    (sorted3Prefix n (3 * n) le_rfl).count c = 3 := by
  have h1 : (sorted3Prefix n (3 * n) le_rfl).count c =
      (Finset.univ.filter (fun i : Fin (3 * n) => (⟨i.val / 3, by omega⟩ : Fin n) = c)).card :=
    count_ofFn _ c
  rw [h1]
  have hset : Finset.univ.filter (fun i : Fin (3 * n) => (⟨i.val / 3, by omega⟩ : Fin n) = c) =
      {⟨3 * c.val, by omega⟩, ⟨3 * c.val + 1, by omega⟩, ⟨3 * c.val + 2, by omega⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [hset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]

def popWhile {n : ℕ} (x : Fin n) : List (Fin n) → List (Fin n) × List (Fin n)
  | [] => ([], [])
  | y :: ys =>
    if y ≤ x then
      let r := popWhile x ys
      (y :: r.1, r.2)
    else
      ([], y :: ys)

lemma popWhile_append {n : ℕ} (x : Fin n) (a b : List (Fin n))
    (ha : ∀ y ∈ a, y ≤ x) (hb : ∀ z ∈ b, x < z) :
    popWhile x (a ++ b) = (a, b) := by
  induction a with
  | nil =>
    cases b with
    | nil => rfl
    | cons z zs =>
      have hzx : x < z := hb z List.mem_cons_self
      simp [popWhile, not_le.mpr hzx]
  | cons y ys ih =>
    have hyx : y ≤ x := ha y List.mem_cons_self
    simp only [List.cons_append, popWhile, if_pos hyx]
    rw [ih (fun u hu => ha u (List.mem_cons_of_mem y hu))]

lemma popWhile_spec {n : ℕ} (x : Fin n) (st : List (Fin n)) :
    (popWhile x st).1 ++ (popWhile x st).2 = st ∧
    (∀ y ∈ (popWhile x st).1, y ≤ x) ∧
    (∀ z, (popWhile x st).2.head? = some z → x < z) := by
  induction st with
  | nil => simp [popWhile]
  | cons y ys ih =>
    simp only [popWhile]
    split_ifs with h
    · refine ⟨by simp [ih.1], ?_, ih.2.2⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact h
      · exact ih.2.1 u hu'
    · refine ⟨rfl, by simp, ?_⟩
      intro z hz
      simp only [List.head?_cons, Option.some.injEq] at hz
      subst hz
      exact lt_of_not_ge h

structure SimState (n : ℕ) where
  st : List (Fin n)
  seen : Finset (Fin n)
  out : List (Fin n)
  path : List Bool

def simStep {n : ℕ} (s : SimState n) (x : Fin n) : SimState n :=
  let pr := popWhile x s.st
  { st := x :: pr.2
    seen := insert x s.seen
    out := s.out ++ pr.1
    path := s.path ++ List.replicate pr.1.length false ++ (if x ∈ s.seen then [] else [true]) }

def simRun {n : ℕ} (w : List (Fin n)) (s : SimState n) : SimState n :=
  w.foldl simStep s

lemma simRun_append {n : ℕ} (w₁ w₂ : List (Fin n)) (s : SimState n) :
    simRun (w₁ ++ w₂) s = simRun w₂ (simRun w₁ s) := by
  simp [simRun, List.foldl_append]

def initState (n : ℕ) : SimState n := ⟨[], ∅, [], []⟩

def stackSort {n : ℕ} (w : List (Fin n)) : List (Fin n) :=
  let s := simRun w (initState n)
  s.out ++ s.st

def wordToDyck {n : ℕ} (w : List (Fin n)) : List Bool :=
  let s := simRun w (initState n)
  s.path ++ List.replicate s.st.length false

lemma simRun_perm {n : ℕ} (w : List (Fin n)) (s : SimState n) :
    ((simRun w s).out ++ (simRun w s).st).Perm (s.out ++ s.st ++ w) := by
  induction w generalizing s with
  | nil => simp [simRun]
  | cons x xs ih =>
    simp only [simRun, List.foldl_cons] at ih ⊢
    refine (ih (simStep s x)).trans ?_
    have hpr := (popWhile_spec x s.st).1
    dsimp [simStep]
    have h1 : (s.out ++ (popWhile x s.st).1 ++ (x :: (popWhile x s.st).2) ++ xs).Perm
        (s.out ++ ((popWhile x s.st).1 ++ (popWhile x s.st).2) ++ (x :: xs)) := by
      simp only [List.append_assoc]
      apply List.Perm.append_left
      apply List.Perm.append_left
      exact List.perm_middle.symm
    rw [hpr] at h1
    simpa [List.append_assoc] using h1

lemma stackSort_perm {n : ℕ} (w : List (Fin n)) : (stackSort w).Perm w := by
  simpa [stackSort, initState] using simRun_perm w (initState n)

/-! Backward map `runBackward` and `dyckToWord` -/

def runBackward (n : ℕ) : List Bool → (k : ℕ) → k ≤ 3 * n → List (Fin n) → List (Fin n)
  | [], _, _, _ => []
  | false :: rest, k, hk, S =>
    if h0 : k = 0 then []
    else
      let k' := k - 1
      let c : Fin n := ⟨k' / 3, by omega⟩
      if k' % 3 = 0 then
        runBackward n rest k' (by omega) (c :: S)
      else
        runBackward n rest k' (by omega) S ++ [c]
  | true :: rest, k, hk, S =>
    match S with
    | [] => []
    | c :: S' => runBackward n rest k hk S' ++ [c]

def dyckToWord (n : ℕ) (p : List Bool) : List (Fin n) :=
  runBackward n p.reverse (3 * n) le_rfl []

/-- Key inductive invariant for `runBackward`: any prefix of a 3-Dyck path is inverted by `simRun`. -/
lemma runBackward_sim (n : ℕ) (pRev : List Bool) (k : ℕ) (hk : k ≤ 3 * n) (S : List (Fin n))
    (hcntF : pRev.count false = k)
    (hpre : ∀ pref, pref <+: pRev.reverse → pref.count false ≤ 3 * pref.count true)
    (hS_sorted : S.Pairwise (· < ·))
    (hS_bound : ∀ z ∈ S, k ≤ 3 * z.val)
    (hbal : 3 * pRev.count true = 3 * S.length + k + (if k % 3 = 0 then 0 else 3 - k % 3)) :
    let w := runBackward n pRev k hk S
    let s := simRun w (initState n)
    ∃ pending : List (Fin n),
      s.st = pending ++ S ∧
      s.out ++ pending = sorted3Prefix n k hk ∧
      s.path ++ List.replicate pending.length false = pRev.reverse ∧
      (∀ c : Fin n, c ∈ s.seen ↔ 3 * c.val < k ∨ c ∈ S) := by
  induction pRev generalizing k S with
  | nil =>
    have hk0 : k = 0 := by simpa using hcntF.symm
    subst hk0
    have hS0 : S = [] := by
      simp only [List.count_nil, mul_zero, Nat.zero_mod, ↓reduceIte, add_zero] at hbal
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hS0
    refine ⟨[], rfl, ?_, rfl, ?_⟩
    · simp [runBackward, simRun, initState, sorted3Prefix]
    · intro c; simp [runBackward, simRun, initState]
  | cons b rest ih =>
    have hpre_rest : ∀ pref, pref <+: rest.reverse → pref.count false ≤ 3 * pref.count true := by
      intro pref hp
      apply hpre pref
      rw [List.reverse_cons]
      exact hp.trans (List.prefix_append _ _)
    cases b with
    | false =>
      have hk_pos : 0 < k := by
        simp only [List.count_cons, beq_self_eq_true, ↓reduceIte] at hcntF; omega
      have hcntF' : rest.count false = k - 1 := by
        simp only [List.count_cons, beq_self_eq_true, ↓reduceIte] at hcntF; omega
      have hcntT' : (false :: rest).count true = rest.count true := by simp
      rw [hcntT'] at hbal
      dsimp only [runBackward]
      rw [dif_neg (by omega : k ≠ 0)]
      set k' := k - 1
      have hk_eq : k = k' + 1 := by omega
      set c : Fin n := ⟨k' / 3, by omega⟩
      by_cases hmod : k' % 3 = 0
      · rw [if_pos hmod]
        have hc_lt : ∀ z ∈ S, c < z := by
          intro z hz
          have := hS_bound z hz
          change k' / 3 < z.val
          omega
        have hS'_sorted : (c :: S).Pairwise (· < ·) := List.pairwise_cons.mpr ⟨hc_lt, hS_sorted⟩
        have hS'_bound : ∀ z ∈ c :: S, k' ≤ 3 * z.val := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · change k' ≤ 3 * (k' / 3); omega
          · have := hS_bound z hz'; omega
        have hbal' : 3 * rest.count true =
            3 * (c :: S).length + k' + (if k' % 3 = 0 then 0 else 3 - k' % 3) := by
          simp only [List.length_cons, hmod, ↓reduceIte, add_zero]
          have hkmod : k % 3 = 1 := by omega
          rw [if_neg (by omega : k % 3 ≠ 0)] at hbal
          omega
        obtain ⟨pending', hst', hout', hpath', hseen'⟩ :=
          ih k' (by omega) (c :: S) hcntF' hpre_rest hS'_sorted hS'_bound hbal'
        refine ⟨pending' ++ [c], ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hst'
        · rw [← List.append_assoc, hout']
          have := sorted3Prefix_succ n k' (by omega)
          simpa [hk_eq, c] using this.symm
        · rw [List.reverse_cons, ← hpath', List.length_append, List.length_singleton,
            List.replicate_succ', List.append_assoc]
        · intro x
          rw [hseen' x]
          simp only [List.mem_cons]
          constructor
          · rintro (h | rfl | h)
            · exact Or.inl (by omega)
            · exact Or.inl (by change 3 * (k' / 3) < k; omega)
            · exact Or.inr h
          · rintro (h | h)
            · by_cases hlt : 3 * x.val < k'
              · exact Or.inl hlt
              · right; left; apply Fin.ext; change x.val = k' / 3; omega
            · exact Or.inr (Or.inr h)
      · rw [if_neg hmod]
        have hS'_bound : ∀ z ∈ S, k' ≤ 3 * z.val := fun z hz => by have := hS_bound z hz; omega
        have hbal' : 3 * rest.count true =
            3 * S.length + k' + (if k' % 3 = 0 then 0 else 3 - k' % 3) := by
          rw [if_neg hmod]
          by_cases hkm : k % 3 = 0
          · rw [if_pos hkm] at hbal; omega
          · rw [if_neg hkm] at hbal; omega
        obtain ⟨pending', hst', hout', hpath', hseen'⟩ :=
          ih k' (by omega) S hcntF' hpre_rest hS_sorted hS'_bound hbal'
        set s0 := simRun (runBackward n rest k' (by omega) S) (initState n)
        have hpop : popWhile c s0.st = (pending', S) := by
          rw [hst']
          apply popWhile_append
          · intro y hy
            have hy_in : y ∈ sorted3Prefix n k' (by omega) := by
              rw [← hout']; exact List.mem_append_right _ hy
            have h3y := sorted3Prefix_mem_lt hy_in
            change y.val ≤ k' / 3; omega
          · intro z hz
            have h3z := hS_bound z hz
            change k' / 3 < z.val; omega
        have hc_seen : c ∈ s0.seen := by
          rw [hseen' c]; left; change 3 * (k' / 3) < k'; omega
        rw [simRun_append]
        change ∃ pending, (simStep s0 c).st = pending ++ S ∧
          (simStep s0 c).out ++ pending = sorted3Prefix n k hk ∧
          (simStep s0 c).path ++ List.replicate pending.length false = (false :: rest).reverse ∧
          ∀ x, x ∈ (simStep s0 c).seen ↔ 3 * x.val < k ∨ x ∈ S
        refine ⟨[c], ?_, ?_, ?_, ?_⟩
        · simp [simStep, hpop]
        · simp only [simStep, hpop, List.append_assoc]
          rw [← List.append_assoc, hout']
          have := sorted3Prefix_succ n k' (by omega)
          simpa [hk_eq, c] using this.symm
        · simp only [simStep, hpop, if_pos hc_seen, List.append_nil, List.length_singleton,
            List.replicate_one, List.reverse_cons]
          rw [hpath']
        · intro x
          simp only [simStep, Finset.mem_insert, hseen' x]
          constructor
          · rintro (rfl | h | h)
            · left; change 3 * (k' / 3) < k; omega
            · left; omega
            · right; exact h
          · rintro (h | h)
            · right; left; omega
            · right; right; exact h
    | true =>
      have hcntF' : rest.count false = k := by simpa using hcntF
      have hcntT' : (true :: rest).count true = rest.count true + 1 := by simp
      have hS_ne : S ≠ [] := by
        intro hnil
        subst hnil
        have hpre_rest_full := hpre rest.reverse (by rw [List.reverse_cons]; exact List.prefix_append _ _)
        rw [List.count_reverse, List.count_reverse, hcntF'] at hpre_rest_full
        rw [hcntT', List.length_nil] at hbal
        split_ifs at hbal <;> omega
      cases S with
      | nil => exact absurd rfl hS_ne
      | cons c S' =>
        dsimp only [runBackward]
        have hS'_sorted : S'.Pairwise (· < ·) := (List.pairwise_cons.mp hS_sorted).2
        have hc_lt_S' : ∀ z ∈ S', c < z := (List.pairwise_cons.mp hS_sorted).1
        have hS'_bound : ∀ z ∈ S', k ≤ 3 * z.val := fun z hz => hS_bound z (List.mem_cons_of_mem c hz)
        have hbal' : 3 * rest.count true =
            3 * S'.length + k + (if k % 3 = 0 then 0 else 3 - k % 3) := by
          rw [hcntT', List.length_cons] at hbal
          omega
        obtain ⟨pending', hst', hout', hpath', hseen'⟩ :=
          ih k hk S' hcntF' hpre_rest hS'_sorted hS'_bound hbal'
        set s0 := simRun (runBackward n rest k hk S') (initState n)
        have hpop : popWhile c s0.st = (pending', S') := by
          rw [hst']
          apply popWhile_append
          · intro y hy
            have hy_in : y ∈ sorted3Prefix n k hk := by
              rw [← hout']; exact List.mem_append_right _ hy
            have h3y := sorted3Prefix_mem_lt hy_in
            have h3c := hS_bound c List.mem_cons_self
            change y.val ≤ c.val; omega
          · exact hc_lt_S'
        have hc_not_seen : c ∉ s0.seen := by
          rw [hseen' c]
          push Not
          refine ⟨hS_bound c List.mem_cons_self, ?_⟩
          intro hmem
          exact lt_irrefl c (hc_lt_S' c hmem)
        rw [simRun_append]
        change ∃ pending, (simStep s0 c).st = pending ++ (c :: S') ∧
          (simStep s0 c).out ++ pending = sorted3Prefix n k hk ∧
          (simStep s0 c).path ++ List.replicate pending.length false = (true :: rest).reverse ∧
          ∀ x, x ∈ (simStep s0 c).seen ↔ 3 * x.val < k ∨ x ∈ c :: S'
        refine ⟨[], ?_, ?_, ?_, ?_⟩
        · simp [simStep, hpop]
        · simp only [simStep, hpop, List.append_nil]; exact hout'
        · simp only [simStep, hpop, if_neg hc_not_seen, List.length_nil, List.replicate_zero,
            List.append_nil, List.reverse_cons]
          rw [hpath']
        · intro x
          simp only [simStep, Finset.mem_insert, hseen' x, List.mem_cons]
          tauto

lemma dyckToWord_stackSort_and_path (n : ℕ) (p : List Bool) (hp : Is3Dyck n p) :
    stackSort (dyckToWord n p) = sorted3Prefix n (3 * n) le_rfl ∧
    wordToDyck (dyckToWord n p) = p := by
  obtain ⟨hlen, hcntT, hpre⟩ := hp
  have hcntF : p.count false = 3 * n := by
    have := bool_list_length p
    omega
  have hpre' : ∀ pref, pref <+: p.reverse.reverse → pref.count false ≤ 3 * pref.count true := by
    intro pref hpref
    rw [List.reverse_reverse] at hpref
    obtain ⟨t, ht⟩ := hpref
    have htake : p.take pref.length = pref := by rw [← ht, List.take_left]
    rw [← htake]
    exact hpre pref.length (by rw [← ht, List.length_append]; omega)
  have hbal : 3 * p.reverse.count true =
      3 * ([] : List (Fin n)).length + 3 * n + (if (3 * n) % 3 = 0 then 0 else 3 - (3 * n) % 3) := by
    rw [List.count_reverse, hcntT, List.length_nil]
    have : (3 * n) % 3 = 0 := by omega
    rw [if_pos this]; omega
  obtain ⟨pending, hst, hout, hpath, _⟩ :=
    runBackward_sim n p.reverse (3 * n) le_rfl [] (by rw [List.count_reverse]; exact hcntF)
      hpre' List.Pairwise.nil (by simp) hbal
  rw [List.append_nil] at hst
  rw [List.reverse_reverse] at hpath
  constructor
  · unfold stackSort dyckToWord
    dsimp only
    rw [hst, hout]
  · unfold wordToDyck dyckToWord
    dsimp only
    rw [hst, hpath]

lemma simRun_preserves_out_order {n : ℕ} (w : List (Fin n)) (s : SimState n) (y : Fin n)
    (hy : y ∈ s.out) : y ∈ (simRun w s).out := by
  induction w generalizing s with
  | nil => exact hy
  | cons x xs ih =>
    apply ih (simStep s x)
    exact List.mem_append_left _ hy

lemma simRun_out_prefix {n : ℕ} (w : List (Fin n)) (s : SimState n) :
    s.out <+: (simRun w s).out := by
  induction w generalizing s with
  | nil => exact List.prefix_refl _
  | cons x xs ih =>
    exact (List.prefix_append s.out _).trans (ih (simStep s x))

/-- If `stackSort w` is sorted (`Pairwise (· ≤ ·)`), then `w` avoids 231 and 221. -/
lemma avoids_of_sorted {n : ℕ} (w : List (Fin n)) (hsort : (stackSort w).Pairwise (· ≤ ·)) :
    ∀ i j k (hi : i < w.length) (hj : j < w.length) (hk : k < w.length),
      i < j → j < k → ¬ (w[k] < w[i] ∧ w[i] ≤ w[j]) := by
  intro i j k hi hj hk hij hjk ⟨hki, hij_val⟩
  -- Split w at j + 1: w = w1 ++ w2 where w1 = w.take (j + 1) and w2 = w.drop (j + 1)
  set w1 := w.take (j + 1)
  set w2 := w.drop (j + 1)
  have hw_eq : w = w1 ++ w2 := (List.take_append_drop (j + 1) w).symm
  -- In simRun w1 (initState n), w[i] is ALREADY in s1.out!
  -- Because w1 = w.take j ++ [w[j]], and w[i] ∈ (s_j.out ++ s_j.st); if w[i] ∈ s_j.st,
  -- since w[i] ≤ w[j] and stack is sorted? Even simpler: popWhile w[j] pops everything ≤ w[j]
  -- from the top, AND the stack is always strictly increasing (Pairwise (· < ·))!
  have hstack_inc : ∀ (u : List (Fin n)) (s : SimState n),
      s.st.Pairwise (· < ·) → (simRun u s).st.Pairwise (· < ·) := by
    intro u
    induction u with
    | nil => intro s hs; exact hs
    | cons x xs ih =>
      intro s hs
      apply ih (simStep s x)
      dsimp only [simStep]
      have hpr := popWhile_spec x s.st
      have hpw : ((popWhile x s.st).1 ++ (popWhile x s.st).2).Pairwise (· < ·) := by
        rw [hpr.1]; exact hs
      have hpw2 : (popWhile x s.st).2.Pairwise (· < ·) := (List.pairwise_append.mp hpw).2.1
      rw [List.pairwise_cons]
      refine ⟨?_, hpw2⟩
      cases h2 : (popWhile x s.st).2 with
      | nil => simp
      | cons z zs =>
        have hxz : x < z := hpr.2.2 z (by rw [h2]; rfl)
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hxz
        · rw [h2] at hpw2
          exact lt_trans hxz ((List.pairwise_cons.mp hpw2).1 u hu')
  set s_j := simRun (w.take j) (initState n)
  have hsj_inc : s_j.st.Pairwise (· < ·) := hstack_inc (w.take j) (initState n) List.Pairwise.nil
  have hwi_in_sj : w[i] ∈ s_j.out ++ s_j.st := by
    have hperm := simRun_perm (w.take j) (initState n)
    simp only [initState, List.nil_append] at hperm
    apply hperm.mem_iff.mpr
    have : w[i] = (w.take j)[i]'(by rw [List.length_take]; omega) := by simp
    rw [this]
    exact List.getElem_mem _
  have hw1_eq : w1 = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem hj
  set s1 := simRun w1 (initState n)
  have hs1_eq : s1 = simStep s_j w[j] := by
    change simRun w1 (initState n) = simStep (simRun (w.take j) (initState n)) w[j]
    rw [hw1_eq, simRun_append]; rfl
  have hwi_in_out1 : w[i] ∈ s1.out := by
    rw [hs1_eq]
    dsimp only [simStep]
    rcases List.mem_append.mp hwi_in_sj with h_out | h_st
    · exact List.mem_append_left _ h_out
    · apply List.mem_append_right
      have hpr := popWhile_spec w[j] s_j.st
      rw [← hpr.1] at h_st
      rcases List.mem_append.mp h_st with h1 | h2
      · exact h1
      · -- Impossible: every element of (popWhile w[j] s_j.st).2 is > w[j] ≥ w[i]!
        exfalso
        cases h2eq : (popWhile w[j] s_j.st).2 with
        | nil => rw [h2eq] at h2; simp at h2
        | cons z zs =>
          have hltz : w[j] < z := hpr.2.2 z (by rw [h2eq]; rfl)
          rw [h2eq] at h2
          rcases List.mem_cons.mp h2 with rfl | hz'
          · exact not_lt.mpr hij_val hltz
          · have hpw : ((popWhile w[j] s_j.st).1 ++ (popWhile w[j] s_j.st).2).Pairwise (· < ·) := by
              rw [hpr.1]; exact hsj_inc
            have hpw2 := (List.pairwise_append.mp hpw).2.1
            rw [h2eq] at hpw2
            have hzu := (List.pairwise_cons.mp hpw2).1 w[i] hz'
            exact not_lt.mpr hij_val (lt_trans hltz hzu)
  -- Meanwhile, w[k] ∈ w2, so w[k] appears in the suffix of (stackSort w) AFTER s1.out!
  have hwk_in_w2 : w[k] ∈ w2 := by
    have : w[k] = w2[k - (j + 1)]'(by simp [w2]; omega) := by
      simp [w2, show j + 1 + (k - (j + 1)) = k by omega]
    rw [this]
    exact List.getElem_mem _
  -- Since stackSort w = s1.out ++ tail where tail is a permutation of s1.st ++ w2:
  have hpre_out : s1.out <+: stackSort w := by
    unfold stackSort
    rw [hw_eq, simRun_append]
    exact (simRun_out_prefix w2 s1).trans (List.prefix_append _ _)
  obtain ⟨tail, htail⟩ := hpre_out
  have htail_perm : tail.Perm (s1.st ++ w2) := by
    have hperm_all := simRun_perm w2 s1
    have hss : stackSort w = (simRun w2 s1).out ++ (simRun w2 s1).st := by
      unfold stackSort; rw [hw_eq, simRun_append]
    rw [← hss, ← htail] at hperm_all
    rw [List.append_assoc] at hperm_all
    exact (List.perm_append_left_iff _).mp hperm_all
  have hwk_in_tail : w[k] ∈ tail := by
    rw [htail_perm.mem_iff]
    exact List.mem_append_right _ hwk_in_w2
  rw [← htail, List.pairwise_append] at hsort
  exact not_lt.mpr (hsort.2.2 w[i] hwi_in_out1 w[k] hwk_in_tail) hki

lemma dyckToWord_valid (n : ℕ) (p : List Bool) (hp : Is3Dyck n p) :
    IsUniformAvoidingList n (dyckToWord n p) := by
  have ⟨hss, _⟩ := dyckToWord_stackSort_and_path n p hp
  have hperm := stackSort_perm (dyckToWord n p)
  rw [hss] at hperm
  constructor
  · intro c
    rw [← hperm.count_eq, sorted3Prefix_count]
  · apply avoids_of_sorted
    rw [hss]
    unfold sorted3Prefix
    rw [List.pairwise_ofFn]
    intro i j hij
    change i.val / 3 ≤ j.val / 3
    exact Nat.div_le_div_right (le_of_lt hij)

/-- Forward invariant: if `w` avoids 231 and 221, `stackSort w` is sorted (`Pairwise (· ≤ ·)`). -/
lemma sorted_of_avoids {n : ℕ} (w : List (Fin n))
    (hav : ∀ i j k (hi : i < w.length) (hj : j < w.length) (hk : k < w.length),
      i < j → j < k → ¬ (w[k] < w[i] ∧ w[i] ≤ w[j])) :
    (stackSort w).Pairwise (· ≤ ·) := by
  -- Stronger invariant by induction on prefix length m ≤ w.length:
  -- For s = simRun (w.take m) (initState n):
  -- (1) s.st.Pairwise (· < ·)
  -- (2) s.out.Pairwise (· ≤ ·)
  -- (3) ∀ y ∈ s.out, ∀ z ∈ s.st, y ≤ z
  -- (4) ∀ y ∈ s.out, ∀ k, m ≤ k → (hk : k < w.length) → y ≤ w[k]
  -- (5) ∀ z ∈ s.st, ∃ i < m, w[i] = z
  have hinv : ∀ m ≤ w.length,
      let s := simRun (w.take m) (initState n)
      s.st.Pairwise (· < ·) ∧
      s.out.Pairwise (· ≤ ·) ∧
      (∀ y ∈ s.out, ∀ z ∈ s.st, y ≤ z) ∧
      (∀ y ∈ s.out, ∀ k (hk : k < w.length), m ≤ k → y ≤ w[k]) ∧
      (∀ z ∈ s.st, ∃ i, ∃ hi : i < w.length, i < m ∧ w[i] = z) := by
    intro m hm
    induction m with
    | zero =>
      simp [simRun, initState]
    | succ m ih =>
      obtain ⟨hst, hout, hout_st, hout_rem, hst_src⟩ := ih (by omega)
      set s := simRun (w.take m) (initState n)
      set x := w[m]'(by omega)
      have htake : w.take (m + 1) = w.take m ++ [x] := List.take_succ_eq_append_getElem (by omega)
      have hstep : simRun (w.take (m + 1)) (initState n) = simStep s x := by
        simp [htake, s, simRun]
      rw [hstep]
      dsimp only [simStep]
      have hpr := popWhile_spec x s.st
      have hpw_split : ((popWhile x s.st).1 ++ (popWhile x s.st).2).Pairwise (· < ·) := by
        rw [hpr.1]; exact hst
      obtain ⟨hpw1, hpw2, hpw12⟩ := List.pairwise_append.mp hpw_split
      have hpop_le_rem : ∀ y ∈ (popWhile x s.st).1, ∀ k (hk : k < w.length), m + 1 ≤ k → y ≤ w[k] := by
        intro y hy k hk hmk
        have hy_st : y ∈ s.st := by rw [← hpr.1]; exact List.mem_append_left _ hy
        obtain ⟨i, hi, him, rfl⟩ := hst_src y hy_st
        have hyx : w[i] ≤ x := hpr.2.1 _ hy
        by_contra hlt
        exact hav i m k hi (by omega) hk him (by omega) ⟨lt_of_not_ge hlt, hyx⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- (1) (x :: pr.2).Pairwise (· < ·)
        rw [List.pairwise_cons]
        refine ⟨?_, hpw2⟩
        cases h2 : (popWhile x s.st).2 with
        | nil => simp
        | cons z zs =>
          have hxz : x < z := hpr.2.2 z (by rw [h2]; rfl)
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact hxz
          · rw [h2] at hpw2
            exact lt_trans hxz ((List.pairwise_cons.mp hpw2).1 u hu')
      · -- (2) (s.out ++ pr.1).Pairwise (· ≤ ·)
        rw [List.pairwise_append]
        refine ⟨hout, hpw1.imp (fun h => le_of_lt h), ?_⟩
        intro y hy z hz
        exact hout_st y hy z (by rw [← hpr.1]; exact List.mem_append_left _ hz)
      · -- (3) ∀ y ∈ s.out ++ pr.1, ∀ z ∈ x :: pr.2, y ≤ z
        intro y hy z hz
        rcases List.mem_append.mp hy with hy_out | hy_pop
        · rcases List.mem_cons.mp hz with rfl | hz_rest
          · exact hout_rem y hy_out m (by omega) le_rfl
          · exact hout_st y hy_out z (by rw [← hpr.1]; exact List.mem_append_right _ hz_rest)
        · rcases List.mem_cons.mp hz with rfl | hz_rest
          · exact hpr.2.1 y hy_pop
          · exact le_of_lt (hpw12 y hy_pop z hz_rest)
      · -- (4) ∀ y ∈ s.out ++ pr.1, ∀ k ≥ m + 1, y ≤ w[k]
        intro y hy k hk hmk
        rcases List.mem_append.mp hy with hy_out | hy_pop
        · exact hout_rem y hy_out k hk (by omega)
        · exact hpop_le_rem y hy_pop k hk hmk
      · -- (5) ∀ z ∈ x :: pr.2, ∃ i < m + 1, w[i] = z
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz_rest
        · exact ⟨m, by omega, by omega, rfl⟩
        · obtain ⟨i, hi, him, rfl⟩ := hst_src z (by rw [← hpr.1]; exact List.mem_append_right _ hz_rest)
          exact ⟨i, hi, by omega, rfl⟩
  obtain ⟨hst, hout, hout_st, _, _⟩ := hinv w.length le_rfl
  rw [List.take_length] at hst hout hout_st
  unfold stackSort
  rw [List.pairwise_append]
  exact ⟨hout, hst.imp (fun h => le_of_lt h), hout_st⟩

lemma sorted_eq_sorted3 {n : ℕ} (w : List (Fin n)) (hcnt : ∀ c : Fin n, w.count c = 3)
    (hsort : (stackSort w).Pairwise (· ≤ ·)) :
    stackSort w = sorted3Prefix n (3 * n) le_rfl := by
  have hperm : (stackSort w).Perm (sorted3Prefix n (3 * n) le_rfl) := by
    rw [List.perm_iff_count]
    intro c
    rw [(stackSort_perm w).count_eq, hcnt c, sorted3Prefix_count]
  have hsort2 : (sorted3Prefix n (3 * n) le_rfl).Pairwise (· ≤ ·) := by
    unfold sorted3Prefix
    rw [List.pairwise_ofFn]
    intro i j hij
    change i.val / 3 ≤ j.val / 3
    exact Nat.div_le_div_right (le_of_lt hij)
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hsort hsort2

lemma wordToDyck_is3Dyck {n : ℕ} (w : List (Fin n)) (hw : IsUniformAvoidingList n w) :
    Is3Dyck n (wordToDyck w) := by
  obtain ⟨hcnt, _⟩ := hw
  have hlen_w : w.length = 3 * n := length_of_count_three w hcnt
  -- Track invariants of simRun on any prefix u of w:
  -- (a) s.path.count false = s.out.length
  -- (b) s.path.count true = s.seen.card
  -- (c) ∀ x ∈ s.out ++ s.st, x ∈ s.seen
  -- (d) ∀ k ≤ s.path.length, (s.path.take k).count false ≤ 3 * (s.path.take k).count true
  have hinv : ∀ u : List (Fin n), (∀ c : Fin n, u.count c ≤ 3) →
      let s := simRun u (initState n)
      s.path.count false = s.out.length ∧
      s.path.count true = s.seen.card ∧
      (∀ x ∈ s.out ++ s.st, x ∈ s.seen) ∧
      (∀ c : Fin n, c ∈ s.seen ↔ c ∈ u) ∧
      (∀ k ≤ s.path.length, (s.path.take k).count false ≤ 3 * (s.path.take k).count true) := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      intro _
      simp [simRun, initState]
    | append_singleton u x ih =>
      intro hu_cnt
      have hu_cnt' : ∀ c : Fin n, u.count c ≤ 3 := fun c => by
        have := hu_cnt c
        rw [List.count_append] at this; omega
      obtain ⟨hF, hT, hmem, hseen, hpre⟩ := ih hu_cnt'
      set s := simRun u (initState n)
      have hrun : simRun (u ++ [x]) (initState n) = simStep s x := by
        simp [simRun_append, s, simRun]
      rw [hrun]
      dsimp only [simStep]
      set pr := popWhile x s.st
      have hpr := popWhile_spec x s.st
      -- Total elements in s.out ++ pr.1 is ≤ 3 * s.seen.card
      have hout_le : (s.out ++ pr.1).length ≤ 3 * s.seen.card := by
        have hperm := simRun_perm u (initState n)
        simp only [initState, List.nil_append] at hperm
        have hsub : (s.out ++ pr.1).length ≤ (s.out ++ s.st).length := by
          rw [← hpr.1]; simp [List.length_append, pr]
        have hu_len : u.length = ∑ c ∈ s.seen, u.count c := by
          rw [← sum_count_eq_length u, ← Finset.sum_subset (Finset.subset_univ s.seen)]
          intro c _ hc
          rw [hseen c] at hc
          exact List.count_eq_zero.mpr hc
        have hle3 : ∑ c ∈ s.seen, u.count c ≤ ∑ _c ∈ s.seen, 3 :=
          Finset.sum_le_sum (fun c _ => hu_cnt' c)
        rw [Finset.sum_const, smul_eq_mul, mul_comm] at hle3
        have hlen_p : (s.out ++ s.st).length = u.length := hperm.length_eq
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- count false
        simp only [List.count_append, List.count_replicate, beq_self_eq_true, ↓reduceIte,
          List.length_append, hF]
        split_ifs <;> simp
      · -- count true
        by_cases hx : x ∈ s.seen
        · rw [if_pos hx, Finset.insert_eq_of_mem hx]
          simp [List.count_append, List.count_replicate, hT]
        · rw [if_neg hx, Finset.card_insert_of_notMem hx]
          simp [List.count_append, List.count_replicate, hT]
      · -- mem seen
        intro y hy
        simp only [Finset.mem_insert]
        rcases List.mem_append.mp hy with h1 | h2
        · rcases List.mem_append.mp h1 with h1a | h1b
          · exact Or.inr (hmem y (List.mem_append_left _ h1a))
          · exact Or.inr (hmem y (List.mem_append_right _ (by rw [← hpr.1]; exact List.mem_append_left _ h1b)))
        · rcases List.mem_cons.mp h2 with rfl | h2b
          · exact Or.inl rfl
          · exact Or.inr (hmem y (List.mem_append_right _ (by rw [← hpr.1]; exact List.mem_append_right _ h2b)))
      · -- seen ↔ mem
        intro c
        simp only [Finset.mem_insert, List.mem_append, List.mem_singleton, hseen c]
        tauto
      · -- prefix condition
        intro k hk
        by_cases hk1 : k ≤ s.path.length
        · rw [List.append_assoc, List.take_append_of_le_length hk1]
          exact hpre k hk1
        · -- k > s.path.length: all of s.path is included, plus some falses, plus maybe a true
          have htake_T : s.path.count true ≤
              ((s.path ++ List.replicate pr.1.length false ++
                if x ∈ s.seen then [] else [true]).take k).count true := by
            have h1 : s.path <+: (s.path ++ List.replicate pr.1.length false ++
                if x ∈ s.seen then [] else [true]).take k := by
              rw [List.append_assoc, List.take_append]
              rw [List.take_of_length_le (by omega)]
              exact List.prefix_append _ _
            exact h1.sublist.count_le true
          have htake_F : ((s.path ++ List.replicate pr.1.length false ++
              if x ∈ s.seen then [] else [true]).take k).count false ≤
              (s.path ++ List.replicate pr.1.length false ++
              if x ∈ s.seen then [] else [true]).count false :=
            (List.take_sublist k _).count_le false
          have hall_F : (s.path ++ List.replicate pr.1.length false ++
              if x ∈ s.seen then [] else [true]).count false = s.out.length + pr.1.length := by
            simp only [List.count_append, List.count_replicate, beq_self_eq_true, ↓reduceIte, hF]
            split_ifs <;> simp
          rw [hall_F] at htake_F
          rw [List.length_append] at hout_le
          omega
  obtain ⟨hF, hT, _, hseen, hpre⟩ := hinv w (fun c => le_of_eq (hcnt c))
  set s := simRun w (initState n)
  have hseen_all : s.seen = Finset.univ := by
    ext c; simp only [Finset.mem_univ, iff_true, hseen c]
    exact List.count_pos_iff.mp (by rw [hcnt c]; omega)
  have hperm := simRun_perm w (initState n)
  simp only [initState, List.nil_append] at hperm
  have hout_st_len : s.out.length + s.st.length = 3 * n := by
    have := hperm.length_eq
    rw [List.length_append, hlen_w] at this
    exact this
  have hpath_T : (wordToDyck w).count true = n := by
    change (s.path ++ List.replicate s.st.length false).count true = n
    simp [List.count_append, List.count_replicate, hT, hseen_all]
  have hpath_F : (wordToDyck w).count false = 3 * n := by
    change (s.path ++ List.replicate s.st.length false).count false = 3 * n
    simp [List.count_append, List.count_replicate, hF, hout_st_len]
  have hpath_len : (wordToDyck w).length = 4 * n := by
    have := bool_list_length (wordToDyck w)
    omega
  refine ⟨hpath_len, hpath_T, ?_⟩
  intro k hk
  change ((s.path ++ List.replicate s.st.length false).take k).count false ≤
    3 * ((s.path ++ List.replicate s.st.length false).take k).count true
  by_cases hk1 : k ≤ s.path.length
  · rw [List.take_append_of_le_length hk1]
    exact hpre k hk1
  · have htake_T : s.path.count true ≤
        ((s.path ++ List.replicate s.st.length false).take k).count true := by
      have h1 : s.path <+: (s.path ++ List.replicate s.st.length false).take k := by
        rw [List.take_append, List.take_of_length_le (by omega)]
        exact List.prefix_append _ _
      exact h1.sublist.count_le true
    have htake_F : ((s.path ++ List.replicate s.st.length false).take k).count false ≤ 3 * n := by
      rw [← hpath_F]; exact (List.take_sublist k _).count_le false
    rw [hT, hseen_all, Finset.card_univ, Fintype.card_fin] at htake_T
    omega

/-- Cleaner: induct on `popped` from the right (`reverseRecOn`). -/
lemma runBackward_pops_all_new {n : ℕ} (pRev : List Bool) (k : ℕ) (popped rest : List (Fin n))
    (hk : k + popped.length ≤ 3 * n)
    (hpop_inc : popped.Pairwise (· < ·))
    (hpop_idx : ∀ i (hi : i < popped.length), popped[i] = ⟨(k + i) / 3, by omega⟩)
    (hpop_all_new : ∀ z ∈ popped, k ≤ 3 * z.val) :
    runBackward n (List.replicate popped.length false ++ pRev) (k + popped.length) hk rest =
      runBackward n pRev k (by omega) (popped ++ rest) := by
  induction popped using List.reverseRecOn generalizing rest with
  | nil => simp
  | append_singleton bs b ih =>
    have hlen : (bs ++ [b]).length = bs.length + 1 := by simp
    have hrep : List.replicate (bs ++ [b]).length false ++ pRev =
        false :: (List.replicate bs.length false ++ pRev) := by
      rw [hlen, List.replicate_succ, List.cons_append]
    rw [hrep]
    have hkb : k + (bs ++ [b]).length = (k + bs.length) + 1 := by omega
    -- Check that b has index (k + bs.length) with (k + bs.length) % 3 = 0!
    have hb_eq : b = ⟨(k + bs.length) / 3, by omega⟩ := by
      have := hpop_idx bs.length (by simp)
      simpa using this
    have hb_mod : (k + bs.length) % 3 = 0 := by
      have hge : k ≤ 3 * b.val := hpop_all_new b (by simp)
      by_cases hbs : bs.length = 0
      · simp only [hbs, add_zero] at hb_eq ⊢
        have : b.val = k / 3 := congrArg Fin.val hb_eq
        omega
      · have hbs_pos : 0 < bs.length := by omega
        have hlt_last : bs[bs.length - 1]'(by omega) < b := by
          have hpw := (List.pairwise_append.mp hpop_inc).2.2
          exact hpw _ (List.getElem_mem _) b (List.mem_singleton_self b)
        have hlast_eq : bs[bs.length - 1]'(by omega) = ⟨(k + (bs.length - 1)) / 3, by omega⟩ := by
          have := hpop_idx (bs.length - 1) (by simp)
          rw [List.getElem_append_left (by omega)] at this
          exact this
        have h1 : (k + (bs.length - 1)) / 3 < (k + bs.length) / 3 := by
          have hv1 : (bs[bs.length - 1]'(by omega)).val = (k + (bs.length - 1)) / 3 :=
            congrArg Fin.val hlast_eq
          have hv2 : b.val = (k + bs.length) / 3 := congrArg Fin.val hb_eq
          have hv3 : (bs[bs.length - 1]'(by omega)).val < b.val := hlt_last
          omega
        omega
    -- Unfold one step of runBackward
    have hstep : runBackward n (false :: (List.replicate bs.length false ++ pRev))
        (k + (bs ++ [b]).length) hk rest =
        runBackward n (List.replicate bs.length false ++ pRev)
          (k + bs.length) (by omega) (b :: rest) := by
      dsimp only [runBackward]
      rw [dif_neg (by omega : k + (bs ++ [b]).length ≠ 0)]
      have hsub : k + (bs ++ [b]).length - 1 = k + bs.length := by omega
      simp only [hsub, hb_mod, ↓reduceIte, ← hb_eq]
    rw [hstep]
    have hbs_inc : bs.Pairwise (· < ·) := (List.pairwise_append.mp hpop_inc).1
    have hbs_idx : ∀ i (hi : i < bs.length), bs[i] = ⟨(k + i) / 3, by omega⟩ := by
      intro i hi
      have := hpop_idx i (by simp; omega)
      rw [List.getElem_append_left hi] at this
      exact this
    have hbs_new : ∀ z ∈ bs, k ≤ 3 * z.val := fun z hz => hpop_all_new z (List.mem_append_left _ hz)
    rw [ih (b :: rest) (by omega) hbs_inc hbs_idx hbs_new]
    simp [List.append_assoc]

/-- Variant when `popped = h :: t` with `3 * h.val < k` (so `h` is a 2nd/3rd copy, popped at `k % 3 ≠ 0`). -/
lemma runBackward_pops_head_old {n : ℕ} (pRev : List Bool) (k : ℕ) (h : Fin n) (t rest : List (Fin n))
    (hk : k + (h :: t).length ≤ 3 * n)
    (hpop_inc : (h :: t).Pairwise (· < ·))
    (hpop_idx : ∀ i (hi : i < (h :: t).length), (h :: t)[i] = ⟨(k + i) / 3, by omega⟩)
    (hh_old : 3 * h.val < k) :
    runBackward n (List.replicate (h :: t).length false ++ pRev) (k + (h :: t).length) hk rest =
      runBackward n pRev k (by omega) (t ++ rest) ++ [h] := by
  have ht_inc : t.Pairwise (· < ·) := (List.pairwise_cons.mp hpop_inc).2
  have hh_lt_t : ∀ z ∈ t, h < z := (List.pairwise_cons.mp hpop_inc).1
  have hk_lt : k < 3 * n := by simp only [List.length_cons] at hk; omega
  have hh_eq : h = ⟨k / 3, by omega⟩ := by
    have := hpop_idx 0 (by simp)
    simpa using this
  have hk_mod : k % 3 ≠ 0 := by
    have : h.val = k / 3 := congrArg Fin.val hh_eq
    omega
  have hk_t : k + 1 + t.length ≤ 3 * n := by simp only [List.length_cons] at hk; omega
  have ht_idx : ∀ i (hi : i < t.length), t[i] = ⟨((k + 1) + i) / 3, by omega⟩ := by
    intro i hi
    have := hpop_idx (i + 1) (by simp; omega)
    simpa [add_assoc, add_comm, add_left_comm] using this
  have ht_new : ∀ z ∈ t, k + 1 ≤ 3 * z.val := by
    intro z hz
    have hhz : h.val < z.val := hh_lt_t z hz
    have : h.val = k / 3 := congrArg Fin.val hh_eq
    omega
  have hrep : List.replicate (h :: t).length false ++ pRev =
      List.replicate t.length false ++ (false :: pRev) := by
    simp only [List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append]
  have hlen_eq : k + (h :: t).length = (k + 1) + t.length := by simp; omega
  have h1 := runBackward_pops_all_new (false :: pRev) (k + 1) t rest (by omega) ht_inc ht_idx ht_new
  have h2 : runBackward n (List.replicate (h :: t).length false ++ pRev) (k + (h :: t).length) hk rest =
      runBackward n (List.replicate t.length false ++ (false :: pRev)) ((k + 1) + t.length) (by omega) rest := by
    congr 1
  rw [h2, h1]
  dsimp only [runBackward]
  rw [dif_neg (by omega : k + 1 ≠ 0)]
  simp only [Nat.add_sub_cancel, hk_mod, ↓reduceIte, ← hh_eq]

lemma popWhile_cons_le {n : ℕ} {x h : Fin n} (t : List (Fin n)) (hle : h ≤ x) :
    popWhile x (h :: t) = (h :: (popWhile x t).1, (popWhile x t).2) := by
  simp [popWhile, hle]

lemma list_getElem_of_eq {α : Type*} {l₁ l₂ : List α} (heq : l₁ = l₂) (i : ℕ) (hi : i < l₂.length) :
    l₂[i] = l₁[i]'(heq ▸ hi) := by
  cases heq; rfl

lemma le_of_two_occ_before {n : ℕ} {w : List (Fin n)} (hw : IsUniformAvoidingList n w)
    {m : ℕ} (hm : m < w.length) {h : Fin n} (hcnt : 2 ≤ (w.take m).count h) :
    h ≤ w[m] := by
  let hfilt := Finset.univ.filter (fun p : Fin m => w[p.val]'(by omega) = h)
  have hcf : hfilt.card = (w.take m).count h := by
    have hwt : w.take m = List.ofFn (fun p : Fin m => w[p.val]'(by omega)) := by
      apply List.ext_getElem (by simp; omega)
      intro i h1 h2; simp
    conv_rhs => rw [hwt]
    exact (count_ofFn _ h).symm
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < hfilt.card)
  simp only [hfilt, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hlt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hltab | hgtab
  · exact hw.2 a.val b.val m (by omega) (by omega) hm hltab b.isLt
      ⟨by rw [ha]; exact lt_of_not_ge hlt, by rw [ha, hb]⟩
  · exact hw.2 b.val a.val m (by omega) (by omega) hm hgtab a.isLt
      ⟨by rw [hb]; exact lt_of_not_ge hlt, by rw [hb, ha]⟩

lemma dyckToWord_wordToDyck_prefix {n : ℕ} (w : List (Fin n)) (hw : IsUniformAvoidingList n w)
    (hsort : (stackSort w).Pairwise (· ≤ ·))
    (hss : stackSort w = sorted3Prefix n (3 * n) le_rfl) :
    ∀ m (hm : m ≤ w.length),
      let s := simRun (w.take m) (initState n)
      ∃ hk : s.out.length ≤ 3 * n,
        s.st.Pairwise (· < ·) ∧
        (∀ y ∈ s.out, ∀ z ∈ s.st, y ≤ z) ∧
        (∀ c : Fin n, c ∈ s.seen ↔ c ∈ w.take m) ∧
        (s.out = sorted3Prefix n s.out.length hk) ∧
        (∀ z ∈ s.st, z ∈ s.seen) ∧
        ((∀ z ∈ s.st, s.out.length ≤ 3 * z.val) →
          runBackward n s.path.reverse s.out.length hk s.st = w.take m) ∧
        (∀ h t, s.st = h :: t → 3 * h.val < s.out.length →
          runBackward n s.path.reverse s.out.length hk t ++ [h] = w.take m) := by
  intro m hm
  induction m with
  | zero =>
    refine ⟨by simp [simRun, initState], by simp [simRun, initState], by simp [simRun, initState],
      by simp [simRun, initState], by simp [simRun, initState, sorted3Prefix],
      by simp [simRun, initState], ?_, ?_⟩
    · intro _; simp [simRun, initState, runBackward]
    · intro h t hst; simp [simRun, initState] at hst
  | succ m ih =>
    obtain ⟨hk, hst_inc, hout_st, hseen_iff, hout_pre, hst_seen, hrb_new, hrb_old⟩ := ih (by omega)
    set s := simRun (w.take m) (initState n)
    set x := w[m]'(by omega)
    have htake : w.take (m + 1) = w.take m ++ [x] := List.take_succ_eq_append_getElem (by omega)
    have hstep : simRun (w.take (m + 1)) (initState n) = simStep s x := by
      simp [htake, s, simRun]
    set pr := popWhile x s.st
    have hpr := popWhile_spec x s.st
    have hpw_split : (pr.1 ++ pr.2).Pairwise (· < ·) := by rw [hpr.1]; exact hst_inc
    obtain ⟨hpw1, hpw2, hpw12⟩ := List.pairwise_append.mp hpw_split
    have hout1_pre_ss : s.out ++ pr.1 <+: sorted3Prefix n (3 * n) le_rfl := by
      rw [← hss]
      have hw_eq : w = w.take (m + 1) ++ w.drop (m + 1) := (List.take_append_drop (m + 1) w).symm
      unfold stackSort
      conv_rhs => rw [hw_eq, simRun_append]
      rw [hstep]
      exact (simRun_out_prefix (w.drop (m + 1)) (simStep s x)).trans (List.prefix_append _ _)
    have hk1 : (s.out ++ pr.1).length ≤ 3 * n := by
      have := hout1_pre_ss.length_le
      simpa [sorted3Prefix] using this
    have hout1_eq : s.out ++ pr.1 = sorted3Prefix n (s.out ++ pr.1).length hk1 := by
      obtain ⟨tl, htl⟩ := hout1_pre_ss
      apply List.ext_getElem (by simp [sorted3Prefix])
      intro i h1 h2
      have hg : (s.out ++ pr.1)[i] = (sorted3Prefix n (3 * n) le_rfl)[i]'(by rw [← htl, List.length_append]; omega) := by
        rw [list_getElem_of_eq htl i _, List.getElem_append_left h1]
      rw [hg]; simp [sorted3Prefix]
    have hlen_ap : s.out.length + pr.1.length ≤ 3 * n := by
      simpa [List.length_append] using hk1
    have hpop_idx : ∀ i (hi : i < pr.1.length), pr.1[i] = ⟨(s.out.length + i) / 3, by omega⟩ := by
      intro i hi
      have h1 : (s.out ++ pr.1)[s.out.length + i]'(by simp; omega) = pr.1[i] := by
        rw [List.getElem_append_right (by omega)]; simp
      rw [← h1]
      have h2 : (s.out ++ pr.1)[s.out.length + i]'(by simp; omega) =
          (sorted3Prefix n (s.out ++ pr.1).length hk1)[s.out.length + i]'(by simp [sorted3Prefix]; omega) := by
        congr 1
      rw [h2]; simp [sorted3Prefix]
    have hrb_after_pops :
        runBackward n ((s.path ++ List.replicate pr.1.length false).reverse)
          (s.out ++ pr.1).length hk1 pr.2 = w.take m := by
      rw [List.reverse_append, List.reverse_replicate]
      by_cases hall : ∀ z ∈ s.st, s.out.length ≤ 3 * z.val
      · have hpop_new : ∀ z ∈ pr.1, s.out.length ≤ 3 * z.val :=
          fun z hz => hall z (by rw [← hpr.1]; exact List.mem_append_left _ hz)
        have h1 := runBackward_pops_all_new s.path.reverse s.out.length pr.1 pr.2
          (by simp at hk1; omega) hpw1 hpop_idx hpop_new
        have h2 : runBackward n (List.replicate pr.1.length false ++ s.path.reverse)
            (s.out ++ pr.1).length hk1 pr.2 =
            runBackward n (List.replicate pr.1.length false ++ s.path.reverse)
              (s.out.length + pr.1.length) (by simp at hk1; omega) pr.2 := by
          congr 1; exact List.length_append
        rw [h2, h1, hpr.1]
        exact hrb_new hall
      · push Not at hall
        obtain ⟨z0, hz0_st, hz0_lt⟩ := hall
        cases hst_eq : s.st with
        | nil => rw [hst_eq] at hz0_st; simp at hz0_st
        | cons h t =>
          have hh_lt : 3 * h.val < s.out.length := by
            rw [hst_eq] at hz0_st hst_inc
            rcases List.mem_cons.mp hz0_st with rfl | hz0_t
            · exact hz0_lt
            · have hhz : h < z0 := (List.pairwise_cons.mp hst_inc).1 z0 hz0_t
              have hz0_in : z0 ∈ s.out := by
                rw [hout_pre, sorted3Prefix, List.mem_ofFn]
                exact ⟨⟨3 * z0.val, hz0_lt⟩, by apply Fin.ext; change 3 * z0.val / 3 = z0.val; omega⟩
              have hle := hout_st z0 hz0_in h (by rw [hst_eq]; exact List.mem_cons_self)
              exact absurd hhz (not_lt.mpr hle)
          have hcnt_ge2 : 2 ≤ (w.take m).count h := by
            have hperm := simRun_perm (w.take m) (initState n)
            simp only [initState, List.nil_append] at hperm
            rw [← hperm.count_eq]
            change 2 ≤ (s.out ++ s.st).count h
            rw [List.count_append]
            have h1 : 1 ≤ s.out.count h := List.count_pos_iff.mpr (by
              rw [hout_pre, sorted3Prefix, List.mem_ofFn]
              exact ⟨⟨3 * h.val, hh_lt⟩, by apply Fin.ext; change 3 * h.val / 3 = h.val; omega⟩)
            have h2 : 1 ≤ s.st.count h := List.count_pos_iff.mpr (by rw [hst_eq]; exact List.mem_cons_self)
            omega
          have hh_le_x : h ≤ x := le_of_two_occ_before hw (by omega) hcnt_ge2
          have hdef : pr = (h :: (popWhile x t).1, (popWhile x t).2) := by
            show popWhile x s.st = _
            rw [hst_eq, popWhile_cons_le t hh_le_x]
          set t1 := (popWhile x t).1
          have hpr1 : pr.1 = h :: t1 := by rw [hdef]
          have ht1_eq : t1 ++ pr.2 = t := by
            have hpr2 : pr.2 = (popWhile x t).2 := by rw [hdef]
            rw [hpr2]; exact (popWhile_spec x t).1
          have h1 := runBackward_pops_head_old s.path.reverse s.out.length h t1 pr.2
            (by rw [← hpr1]; simp at hk1; omega)
            (by rw [← hpr1]; exact hpw1)
            (by intro i hi; rw [list_getElem_of_eq hpr1 i hi]; exact hpop_idx i _)
            hh_lt
          have h2 : runBackward n (List.replicate pr.1.length false ++ s.path.reverse)
              (s.out ++ pr.1).length hk1 pr.2 =
              runBackward n (List.replicate (h :: t1).length false ++ s.path.reverse)
                (s.out.length + (h :: t1).length) (by rw [← hpr1]; simp at hk1; omega) pr.2 := by
            congr 1
            · rw [hpr1]
            · rw [List.length_append, hpr1]
          rw [h2, h1, ht1_eq]
          exact hrb_old h t hst_eq hh_lt
    rw [hstep]
    refine ⟨hk1, ?_, ?_, ?_, hout1_eq, ?_, ?_, ?_⟩
    · dsimp only [simStep]
      rw [List.pairwise_cons]
      refine ⟨?_, hpw2⟩
      cases h2 : pr.2 with
      | nil => simp
      | cons z zs =>
        have hxz : x < z := hpr.2.2 z (by rw [h2]; rfl)
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hxz
        · rw [h2] at hpw2
          exact lt_trans hxz ((List.pairwise_cons.mp hpw2).1 u hu')
    · dsimp only [simStep]
      intro y hy z hz
      rcases List.mem_append.mp hy with hy_out | hy_pop
      · rcases List.mem_cons.mp hz with rfl | hz_rest
        · have hpre_out : s.out <+: stackSort w := by
            have hw_eq : w = w.take m ++ w.drop m := (List.take_append_drop m w).symm
            unfold stackSort
            conv_rhs => rw [hw_eq, simRun_append]
            exact (simRun_out_prefix (w.drop m) s).trans (List.prefix_append _ _)
          obtain ⟨tl, htl⟩ := hpre_out
          have htl_perm : tl.Perm (s.st ++ w.drop m) := by
            have hpa := simRun_perm (w.drop m) s
            have hss' : stackSort w = (simRun (w.drop m) s).out ++ (simRun (w.drop m) s).st := by
              have hw_eq : w = w.take m ++ w.drop m := (List.take_append_drop m w).symm
              unfold stackSort
              conv_lhs => rw [hw_eq, simRun_append]
            rw [← hss', ← htl, List.append_assoc] at hpa
            exact (List.perm_append_left_iff _).mp hpa
          have hx_tl : x ∈ tl := by
            rw [htl_perm.mem_iff]
            apply List.mem_append_right
            have : x = (w.drop m)[0]'(by simp; omega) := by simp [x]
            rw [this]; exact List.getElem_mem _
          rw [← htl, List.pairwise_append] at hsort
          exact hsort.2.2 y hy_out x hx_tl
        · exact hout_st y hy_out z (by rw [← hpr.1]; exact List.mem_append_right _ hz_rest)
      · rcases List.mem_cons.mp hz with rfl | hz_rest
        · exact hpr.2.1 y hy_pop
        · exact le_of_lt (hpw12 y hy_pop z hz_rest)
    · dsimp only [simStep]
      intro c
      rw [htake, Finset.mem_insert, List.mem_append, List.mem_singleton, hseen_iff c]
      tauto
    · dsimp only [simStep]
      intro z hz
      simp only [Finset.mem_insert]
      rcases List.mem_cons.mp hz with rfl | hz_rest
      · exact Or.inl rfl
      · exact Or.inr (hst_seen z (by rw [← hpr.1]; exact List.mem_append_right _ hz_rest))
    · dsimp only [simStep]
      intro hall_new
      have hx_new : (s.out ++ pr.1).length ≤ 3 * x.val := hall_new x List.mem_cons_self
      have hx_not_seen : x ∉ s.seen := by
        rw [hseen_iff x]
        intro hx_mem
        have hperm := simRun_perm (w.take m) (initState n)
        simp only [initState, List.nil_append] at hperm
        rw [← hperm.mem_iff] at hx_mem
        change x ∈ s.out ++ s.st at hx_mem
        rw [← hpr.1, ← List.append_assoc] at hx_mem
        rcases List.mem_append.mp hx_mem with hx1 | hx2
        · rw [hout1_eq] at hx1
          have := sorted3Prefix_mem_lt hx1
          omega
        · cases h2 : pr.2 with
          | nil => rw [h2] at hx2; simp at hx2
          | cons z zs =>
            have hxz : x < z := hpr.2.2 z (by rw [h2]; rfl)
            rw [h2] at hx2
            rcases List.mem_cons.mp hx2 with rfl | hx2'
            · exact lt_irrefl x hxz
            · rw [h2] at hpw2
              exact lt_irrefl x (lt_trans hxz ((List.pairwise_cons.mp hpw2).1 x hx2'))
      rw [if_neg hx_not_seen, List.reverse_append, List.reverse_singleton, List.singleton_append]
      dsimp only [runBackward]
      rw [hrb_after_pops, htake]
    · dsimp only [simStep]
      intro h t hcons hh_old
      cases hcons
      have hx_seen : x ∈ s.seen := by
        have hx_in : x ∈ s.out ++ pr.1 := by
          rw [hout1_eq, sorted3Prefix, List.mem_ofFn]
          exact ⟨⟨3 * x.val, hh_old⟩, by apply Fin.ext; change 3 * x.val / 3 = x.val; omega⟩
        have hperm := simRun_perm (w.take m) (initState n)
        simp only [initState, List.nil_append] at hperm
        rw [hseen_iff x, ← hperm.mem_iff]
        change x ∈ s.out ++ s.st
        rw [← hpr.1, ← List.append_assoc]
        exact List.mem_append_left _ hx_in
      rw [if_pos hx_seen, List.append_nil]
      change runBackward n (s.path ++ List.replicate pr.1.length false).reverse
          (s.out ++ pr.1).length hk1 pr.2 ++ [x] = w.take (m + 1)
      rw [hrb_after_pops, htake]

/-- Key left-inverse lemma: `dyckToWord n (wordToDyck w) = w` for uniform avoiding words. -/
lemma dyckToWord_wordToDyck {n : ℕ} (w : List (Fin n)) (hw : IsUniformAvoidingList n w) :
    dyckToWord n (wordToDyck w) = w := by
  have hsort : (stackSort w).Pairwise (· ≤ ·) := sorted_of_avoids w hw.2
  have hss : stackSort w = sorted3Prefix n (3 * n) le_rfl := sorted_eq_sorted3 w hw.1 hsort
  have hfull := dyckToWord_wordToDyck_prefix w hw hsort hss w.length le_rfl
  rw [List.take_length] at hfull
  obtain ⟨hk, hst_inc, hout_st, _, hout_pre, _, hrb_new, hrb_old⟩ := hfull
  set s := simRun w (initState n)
  have hst_len : s.out.length + s.st.length = 3 * n := by
    have := congrArg List.length hss
    simpa [stackSort, sorted3Prefix] using this
  have hst_idx : ∀ i (hi : i < s.st.length), s.st[i] = ⟨(s.out.length + i) / 3, by omega⟩ := by
    intro i hi
    have h1 : (s.out ++ s.st)[s.out.length + i]'(by simp; omega) = s.st[i] := by
      rw [List.getElem_append_right (by omega)]; simp
    rw [← h1]
    have h2 : (s.out ++ s.st)[s.out.length + i]'(by simp; omega) =
        (sorted3Prefix n (3 * n) le_rfl)[s.out.length + i]'(by simp [sorted3Prefix]; omega) := by
      congr 1
    rw [h2]; simp [sorted3Prefix]
  unfold dyckToWord wordToDyck
  dsimp only
  rw [List.reverse_append, List.reverse_replicate]
  by_cases hall : ∀ z ∈ s.st, s.out.length ≤ 3 * z.val
  · have h1 := runBackward_pops_all_new s.path.reverse s.out.length s.st [] (by omega) hst_inc hst_idx hall
    have h2 : runBackward n (List.replicate s.st.length false ++ s.path.reverse) (3 * n) le_rfl [] =
        runBackward n (List.replicate s.st.length false ++ s.path.reverse)
          (s.out.length + s.st.length) (by omega) [] := by congr 1; exact hst_len.symm
    rw [h2, h1, List.append_nil]
    exact hrb_new hall
  · push Not at hall
    obtain ⟨z0, hz0_st, hz0_lt⟩ := hall
    cases hst_eq : s.st with
    | nil => rw [hst_eq] at hz0_st; simp at hz0_st
    | cons h t =>
      have hh_lt : 3 * h.val < s.out.length := by
        rw [hst_eq] at hz0_st hst_inc
        rcases List.mem_cons.mp hz0_st with rfl | hz0_t
        · exact hz0_lt
        · have hhz : h < z0 := (List.pairwise_cons.mp hst_inc).1 z0 hz0_t
          have hz0_in : z0 ∈ s.out := by
            rw [hout_pre, sorted3Prefix, List.mem_ofFn]
            exact ⟨⟨3 * z0.val, hz0_lt⟩, by apply Fin.ext; change 3 * z0.val / 3 = z0.val; omega⟩
          have hle := hout_st z0 hz0_in h (by rw [hst_eq]; exact List.mem_cons_self)
          exact absurd hhz (not_lt.mpr hle)
      have h1 := runBackward_pops_head_old s.path.reverse s.out.length h t []
        (by rw [← hst_eq]; omega)
        (by rw [← hst_eq]; exact hst_inc)
        (by intro i hi; rw [list_getElem_of_eq hst_eq i hi]; exact hst_idx i _)
        hh_lt
      have h2 : runBackward n (List.replicate (h :: t).length false ++ s.path.reverse) (3 * n) le_rfl [] =
          runBackward n (List.replicate (h :: t).length false ++ s.path.reverse)
            (s.out.length + (h :: t).length) (by rw [← hst_eq]; omega) [] := by
        congr 1; rw [← hst_eq]; exact hst_len.symm
      rw [h2, h1, List.append_nil]
      exact hrb_old h t hst_eq hh_lt

def listEquivDyck (n : ℕ) :
    {w : List (Fin n) // IsUniformAvoidingList n w} ≃ {p : List Bool // Is3Dyck n p} where
  toFun := fun ⟨w, hw⟩ => ⟨wordToDyck w, wordToDyck_is3Dyck w hw⟩
  invFun := fun ⟨p, hp⟩ => ⟨dyckToWord n p, dyckToWord_valid n p hp⟩
  left_inv := fun ⟨w, hw⟩ => Subtype.ext (dyckToWord_wordToDyck w hw)
  right_inv := fun ⟨p, hp⟩ => Subtype.ext (dyckToWord_stackSort_and_path n p hp).2

end OMA.P_oeis_a002293

theorem OMA.solution : type_of% @OMA.S_oeis_a002293.main := by
  intro n
  rw [Nat.card_congr (OMA.P_oeis_a002293.wordEquivList n),
    Nat.card_congr (OMA.P_oeis_a002293.listEquivDyck n),
    OMA.P_oeis_a002293.card_is3Dyck n]
