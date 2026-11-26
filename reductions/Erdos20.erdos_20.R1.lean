import FormalConjectures.ErdosProblems.«20»
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Union

-- Reduction Erdos20.erdos_20.R1 of Erdős Problem 20
-- Credit: @kenanwienberg

/-!
# Reduction of Erdős Problem 20 (Sunflower Conjecture)

Splits `Erdos20.erdos_20` along the rainbow-coloring and word-sunflower transfer
used in OpenAI (Nov 24, 2026), *An exponential bound for sunflowers*:
- `H1`: color-coding lemma extracting a rainbow subfamily of fraction at least `n! / n^n`.
- `H2`: fixed-base exponential bound for `r`-sunflower-free word families over arbitrary finite alphabets.
-/

namespace OMA.R_Erdos20_erdos_20_R1

def H1 : Prop :=
  ∀ (α : Type) (n : ℕ), 0 < n →
    ∀ (F : Finset (Finset α)), (∀ A ∈ F, A.card = n) →
      ∃ (c : α → Fin n) (G : Finset (Finset α)),
        G ⊆ F ∧
        (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
        F.card * n.factorial ≤ G.card * n ^ n

def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r →
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (n m : ℕ) (W : Finset (Fin n → Fin m)),
      (∀ w : Fin r → Fin n → Fin m,
        (∀ i, w i ∈ W) →
        (∀ j : Fin n, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b) →
      W.card ≤ D ^ n

lemma pow_self_le_three_pow_mul_factorial (n : ℕ) :
    n ^ n ≤ 3 ^ n * n.factorial := by
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hExp : Real.exp n ≤ (3 : ℝ) ^ n := by
    calc
      Real.exp n = (Real.exp 1) ^ n := by simp [← Real.exp_nat_mul]
      _ ≤ (3 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h := (div_le_iff₀ hn).mp
    ((Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n).trans hExp)
  exact_mod_cast h

lemma pow_add_one_lt_add_two_pow {a n : ℕ} (ha : 1 ≤ a) (hn : 0 < n) :
    a ^ n + 1 < (a + 2) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h1 : a ^ (m + 1) + 2 ≤ (a + 2) ^ (m + 1) := ih (Nat.succ_pos m)
    have h2 : (a ^ (m + 1) + 2) * a ≤ (a + 2) ^ (m + 1) * (a + 2) :=
      Nat.mul_le_mul h1 (Nat.le_add_right a 2)
    have h3 : a ^ (m + 2) + 2 ≤ (a ^ (m + 1) + 2) * a := by
      rw [pow_succ, add_mul]
      omega
    have h4 : a ^ (m + 2) + 2 ≤ (a + 2) ^ (m + 2) := by
      rw [pow_succ (a + 2)]
      exact h3.trans h2
    exact Nat.lt_of_succ_le h4

lemma f_le_of_forall {n k m : ℕ}
    (hm : ∀ {α : Type}, ∀ (F : Set (Set α)),
      ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) →
      ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S) :
    Erdos20.f n k ≤ m :=
  Nat.sInf_le hm

lemma f_zero_eq_zero (n : ℕ) : Erdos20.f n 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply f_le_of_forall
  intro α F _
  exact ⟨∅, Set.empty_subset _, by simp, isSunflower_empty⟩

lemma f_one_le_one (n : ℕ) : Erdos20.f n 1 ≤ 1 := by
  apply f_le_of_forall
  intro α F hF
  obtain ⟨A, hA⟩ := F.nonempty_of_ncard_ne_zero (by omega)
  exact ⟨{A}, Set.singleton_subset_iff.mpr hA, by simp, isSunflower_singleton A⟩

lemma f_two_le_two (n : ℕ) : Erdos20.f n 2 ≤ 2 := by
  apply f_le_of_forall
  intro α F hF
  have hfin : F.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hcard : 1 < F.ncard := by omega
  obtain ⟨A, B, hA, hB, hAB⟩ := (Set.one_lt_ncard_iff hfin).mp hcard
  refine ⟨{A, B}, ?_, ?_, ?_⟩
  · intro X hX
    rcases hX with rfl | rfl
    · exact hA
    · exact hB
  · exact Set.ncard_pair hAB
  · refine ⟨A ∩ B, ?_⟩
    intro X hX Y hY hXY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact (hXY rfl).elim
    · rfl
    · exact Set.inter_comm _ _
    · exact (hXY rfl).elim

lemma word_family_of_rainbow {α : Type} [DecidableEq α] {n r : ℕ}
    {G F : Finset (Finset α)} (hGF : G ⊆ F) (c : α → Fin n)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x))
    (hfree : ¬ ∃ S ⊆ F, S.card = r ∧ ∃ K : Finset α,
      ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K) :
    ∃ (m : ℕ) (W : Finset (Fin n → Fin m)),
      W.card = G.card ∧
      ∀ w : Fin r → Fin n → Fin m,
        (∀ i, w i ∈ W) →
        (∀ j : Fin n, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b := by
  classical
  let U : Finset α := G.biUnion id
  let e (A : G) : (A : Finset α) ≃ Fin n := Equiv.ofBijective _ (hc A A.property)
  let pt (A : G) (j : Fin n) : U :=
    ⟨(e A).symm j, Finset.mem_biUnion.mpr ⟨A, A.property, ((e A).symm j).property⟩⟩
  let encode (A : G) (j : Fin n) : Fin U.card := U.equivFin (pt A j)
  let decode (u : Fin U.card) : α := U.equivFin.symm u
  have hdec_inj : Function.Injective decode :=
    Subtype.val_injective.comp U.equivFin.symm.injective
  have hmem : ∀ (A : G) (x : α), x ∈ (A : Finset α) ↔ decode (encode A (c x)) = x := by
    intro A x
    have hdecode (j : Fin n) : decode (encode A j) = ((e A).symm j).val := by
      simp [decode, encode, pt]
    rw [hdecode]
    constructor
    · intro hx
      have he : (e A) ⟨x, hx⟩ = c x := rfl
      rw [← he, Equiv.symm_apply_apply]
    · intro hx
      exact hx ▸ ((e A).symm (c x)).property
  have henc_inj : Function.Injective encode := by
    intro A B hab
    apply Subtype.ext
    ext x
    rw [hmem, hmem, hab]
  let W : Finset (Fin n → Fin U.card) := Finset.univ.image encode
  refine ⟨U.card, W, ?_, ?_⟩
  · simp [W, Finset.card_image_of_injective _ henc_inj]
  · intro w hw hadm
    by_contra hnc
    push Not at hnc
    obtain ⟨a₀, b₀, hab₀⟩ := hnc
    have hwinj : Function.Injective w := by
      intro i j hij
      by_contra hne
      apply hab₀
      funext j₀
      rcases hadm j₀ with hconst | hinj
      · exact hconst a₀ b₀
      · exact (hne (hinj (congrFun hij j₀))).elim
    have hlift : ∀ i : Fin r, ∃ A : G, encode A = w i := by
      intro i
      obtain ⟨A, _, hA⟩ := Finset.mem_image.mp (hw i)
      exact ⟨A, hA⟩
    choose A hA using hlift
    have hAinj : Function.Injective (fun i : Fin r => (A i : Finset α)) := by
      intro i j hij
      apply hwinj
      rw [← hA i, ← hA j, Subtype.ext hij]
    have hAmem (i : Fin r) (x : α) :
        x ∈ (A i : Finset α) ↔ decode (w i (c x)) = x := by
      rw [← hA i, hmem]
    let K : Finset α := U.filter fun x => ∀ i : Fin r, x ∈ (A i : Finset α)
    let emb : Fin r ↪ Finset α := ⟨fun i => (A i : Finset α), hAinj⟩
    apply hfree
    refine ⟨Finset.univ.map emb, ?_, by simp, K, ?_⟩
    · intro X hX
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hX
      exact hGF (A i).property
    · intro X hX Y hY hXY
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hX
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hY
      have hij : i ≠ j := fun h => hXY (congrArg emb h)
      ext x
      constructor
      · intro hx
        obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨A i, (A i).property, hi⟩, ?_⟩
        have heq : w i (c x) = w j (c x) :=
          hdec_inj (((hAmem i x).mp hi).trans ((hAmem j x).mp hj).symm)
        rcases hadm (c x) with hconst | hinj
        · intro t
          exact (hAmem t x).mpr ((congrArg decode (hconst t i)).trans ((hAmem i x).mp hi))
        · exact (hij (hinj heq)).elim
      · intro hx
        have hall := (Finset.mem_filter.mp hx).2
        exact Finset.mem_inter.mpr ⟨hall i, hall j⟩

lemma f_le_of_wordBound (h1 : H1) {r D : ℕ}
    (hWord : ∀ (n m : ℕ) (W : Finset (Fin n → Fin m)),
      (∀ w : Fin r → Fin n → Fin m,
        (∀ i, w i ∈ W) →
        (∀ j : Fin n, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b) →
      W.card ≤ D ^ n)
    {n : ℕ} (hn : 0 < n) :
    Erdos20.f n r ≤ (3 * D) ^ n + 1 := by
  classical
  apply f_le_of_forall
  intro α F ⟨hFn, hFcard⟩
  have hFfin : F.Finite := Set.finite_of_ncard_ne_zero (by omega)
  let toFin : Set α → Finset α := fun A => if h : A.Finite then h.toFinset else ∅
  have htoFin_coe : ∀ A ∈ F, (toFin A : Set α) = A := by
    intro A hA
    have hAfin : A.Finite := Set.finite_of_ncard_ne_zero (by
      have := hFn A hA
      omega)
    simp [toFin, hAfin]
  let F' : Finset (Finset α) := hFfin.toFinset.image toFin
  have hF'_card : F'.card = F.ncard := by
    rw [Finset.card_image_of_injOn, Set.ncard_eq_toFinset_card F hFfin]
    intro A hA B hB hAB
    have hA' : A ∈ F := (Set.Finite.mem_toFinset hFfin).mp hA
    have hB' : B ∈ F := (Set.Finite.mem_toFinset hFfin).mp hB
    rw [← htoFin_coe A hA', ← htoFin_coe B hB', hAB]
  have hF'_unif : ∀ A ∈ F', A.card = n := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    have hB' : B ∈ F := (Set.Finite.mem_toFinset hFfin).mp hB
    have hBfin : B.Finite := Set.finite_of_ncard_ne_zero (by
      have := hFn B hB'
      omega)
    have hcardB : (toFin B).card = B.ncard := by
      rw [Set.ncard_eq_toFinset_card B hBfin]
      simp [toFin, hBfin]
    exact hcardB.trans (hFn B hB')
  by_contra hno
  have hfree : ¬ ∃ S ⊆ F', S.card = r ∧ ∃ K : Finset α,
      ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K := by
    rintro ⟨S', hS'F', hS'card, K, hK⟩
    apply hno
    let S : Set (Set α) := (fun A : Finset α => (A : Set α)) '' (S' : Set (Finset α))
    refine ⟨S, ?_, ?_, ?_⟩
    · intro X hX
      obtain ⟨A, hA, rfl⟩ := hX
      obtain ⟨B, hB, hBA⟩ := Finset.mem_image.mp (hS'F' hA)
      have hB' : B ∈ F := (Set.Finite.mem_toFinset hFfin).mp hB
      change (A : Set α) ∈ F
      rw [← hBA, htoFin_coe B hB']
      exact hB'
    · rw [Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset, hS'card]
    · refine ⟨(K : Set α), ?_⟩
      intro X hX Y hY hXY
      obtain ⟨A, hA, rfl⟩ := hX
      obtain ⟨B, hB, rfl⟩ := hY
      have hAB : A ≠ B := fun h => hXY (congrArg (fun Z : Finset α => (Z : Set α)) h)
      rw [← Finset.coe_inter, hK A hA B hB hAB]
  obtain ⟨c, G, hGF, hc, hcount⟩ := h1 α n hn F' hF'_unif
  obtain ⟨m, W, hWcard, hWfree⟩ := word_family_of_rainbow hGF c hc hfree
  have hGbound : G.card ≤ D ^ n := hWcard ▸ hWord n m W hWfree
  have hF'bound : F'.card ≤ (3 * D) ^ n := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.factorial_pos n)
    calc
      F'.card * n.factorial ≤ G.card * n ^ n := hcount
      _ ≤ D ^ n * (3 ^ n * n.factorial) :=
        Nat.mul_le_mul hGbound (pow_self_le_three_pow_mul_factorial n)
      _ = (3 * D) ^ n * n.factorial := by rw [mul_pow]; ring
  omega

theorem main : H1 → H2 → type_of% @Erdos20.erdos_20 := by
  intro h1 h2
  classical
  let c : ℕ → ℕ := fun k =>
    if hk : 3 ≤ k then 3 * (h2 k hk).choose + 2 else k + 1
  refine ⟨c, ?_⟩
  intro n k hn
  by_cases hk : 3 ≤ k
  · have hD : 1 ≤ (h2 k hk).choose := (h2 k hk).choose_spec.1
    have hWord := (h2 k hk).choose_spec.2
    have hf : Erdos20.f n k ≤ (3 * (h2 k hk).choose) ^ n + 1 :=
      f_le_of_wordBound h1 hWord hn
    have hlt : (3 * (h2 k hk).choose) ^ n + 1 < (3 * (h2 k hk).choose + 2) ^ n :=
      pow_add_one_lt_add_two_pow (by omega) hn
    simpa [c, hk] using lt_of_le_of_lt hf hlt
  · have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp only [c, hk, ↓reduceDIte, zero_add, one_pow]
      rw [f_zero_eq_zero]
      exact Nat.zero_lt_one
    · simp only [c, hk, ↓reduceDIte]
      have hpow : 1 < (1 + 1) ^ n := by
        calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      exact lt_of_le_of_lt (f_one_le_one n) hpow
    · simp only [c, hk, ↓reduceDIte]
      have hpow : 2 < (2 + 1) ^ n := by
        calc 2 < 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      exact lt_of_le_of_lt (f_two_le_two n) hpow

end OMA.R_Erdos20_erdos_20_R1
