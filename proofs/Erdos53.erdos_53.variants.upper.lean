import FormalConjectures.ErdosProblems.«53»

-- Problem: Erdős Problem 53 — upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/53.lean:80 (declaration Erdos53.erdos_53.variants.upper)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Sums and products of distinct elements: the Erdős–Szemerédi upper construction

Take the primes `p ≤ 16^j`, say `k` of them (Chebyshev gives `k ≥ 2^j`), and let `A` be the
`k^k` numbers `∏ p^(e p)` with every exponent below `k`. Every subset sum lies in an interval of
length `k^k · (k^4)^(k^2)`, and every subset product has the form `∏ p^(f p)` with `f p ≤ k^k · k`.
So at most `k^(6 k^2)` integers are sums or products, which is `exp(6 k^2 log k)`, and this is
at most `exp(12 (log |A|)^2 / log log |A|)` since `log |A| = k log k`.
-/

namespace OMA53

lemma nat_ineq (j : ℕ) (hj : 2 ≤ j) : 4 * j * 2 ^ j + 4 * j + 1 ≤ 16 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 2 ^ n ≤ 16 ^ n := Nat.pow_le_pow_left (by norm_num) n
    have h3 : 2 ^ n ≤ n * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)
    rw [pow_succ, pow_succ]; nlinarith
lemma pi_big (j : ℕ) (hj : 2 ≤ j) : 2 ^ j ≤ Nat.primeCounting (16 ^ j) := by
  have h := Chebyshev.pi_ge (16 ^ j)
  have hpos : (0:ℝ) < Real.log ((16:ℕ) ^ j : ℕ) := by
    apply Real.log_pos; norm_cast; exact Nat.one_lt_pow (by omega) (by norm_num)
  have hlog : Real.log (((16 ^ j : ℕ) : ℝ)) = 4 * j * Real.log 2 := by
    push_cast; rw [Real.log_pow, show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log (((16 ^ j : ℕ) : ℝ) + 1) ≤ (4 * j + 1) * Real.log 2 := by
    have : ((16 ^ j : ℕ) : ℝ) + 1 ≤ 2 ^ (4 * j + 1) := by
      push_cast; rw [pow_succ, pow_mul]; norm_num
      have : (1:ℝ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
      linarith
    calc Real.log (((16 ^ j : ℕ) : ℝ) + 1) ≤ Real.log (2 ^ (4 * j + 1)) :=
          Real.log_le_log (by positivity) this
      _ = _ := by rw [Real.log_pow]; push_cast; ring
  have hn := nat_ineq j hj
  have hn' : (4 * j * 2 ^ j + 4 * j + 1 : ℝ) ≤ 16 ^ j := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ((2 ^ j : ℕ) : ℝ) ≤ ((16 ^ j : ℕ) * Real.log 2 - Real.log ((16 ^ j : ℕ) + 1)) / Real.log ((16 ^ j : ℕ) : ℝ) := by
    rw [le_div_iff₀ hpos, hlog]
    have : ((16 ^ j : ℕ) : ℝ) = 16 ^ j := by push_cast; rfl
    rw [this] at hlog2 ⊢; push_cast
    nlinarith [mul_le_mul_of_nonneg_right hn' hl2.le]
  exact_mod_cast key.trans h


section
variable (Q : Finset ℕ)

def En {t : ℕ} (e : Q → Fin t) : ℕ := ∏ p : Q, (p : ℕ) ^ (e p : ℕ)

lemma En_fact {t : ℕ} (hQ : ∀ p ∈ Q, p.Prime) (e : Q → Fin t) (q : Q) :
    (En Q e).factorization q = e q := by
  unfold En
  rw [Nat.factorization_prod (fun (p : Q) _ => pow_ne_zero _ (hQ p p.2).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  simp_rw [Nat.Prime.factorization_pow (hQ _ (Subtype.prop _)), Finsupp.single_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ hb; rw [if_neg]; exact fun h => hb (Subtype.ext h)
  · simp

lemma En_inj {t : ℕ} (hQ : ∀ p ∈ Q, p.Prime) : Function.Injective (En Q (t := t)) := by
  intro e e' h
  funext q
  apply Fin.ext
  rw [← En_fact Q hQ e q, ← En_fact Q hQ e' q, h]

lemma En_le {t B : ℕ} (hB1 : 1 ≤ B) (hB : ∀ p ∈ Q, p ≤ B) (e : Q → Fin t) :
    En Q e ≤ B ^ (t * Q.card) := by
  unfold En
  calc ∏ p : Q, (p : ℕ) ^ (e p : ℕ) ≤ (B ^ t) ^ (Finset.univ : Finset Q).card := by
        apply Finset.prod_le_pow_card
        intro p _
        calc (p : ℕ) ^ (e p : ℕ) ≤ B ^ (e p : ℕ) := Nat.pow_le_pow_left (hB p p.2) _
          _ ≤ B ^ t := Nat.pow_le_pow_right hB1 (e p).2.le
    _ = B ^ (t * Q.card) := by rw [Finset.card_univ, Fintype.card_coe, pow_mul]

def Aset (t : ℕ) : Finset ℤ := (Finset.univ : Finset (Q → Fin t)).image (fun e => ((En Q e : ℕ) : ℤ))

lemma Aset_card {t : ℕ} (hQ : ∀ p ∈ Q, p.Prime) : (Aset Q t).card = t ^ Q.card := by
  unfold Aset
  rw [Finset.card_image_of_injective _ (fun a b h => En_inj Q hQ (Nat.cast_injective h)),
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

lemma prod_form {t : ℕ} (S : Finset ℤ) (hS : S ⊆ Aset Q t) :
    ∃ f : Q → ℕ, (∀ p, f p ≤ S.card * t) ∧ ∏ b ∈ S, b = ∏ p : Q, ((p : ℕ) : ℤ) ^ (f p) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, fun _ => by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨f, hf, hprod⟩ := ih ((Finset.subset_insert _ _).trans hS)
    have haA : a ∈ Aset Q t := hS (Finset.mem_insert_self _ _)
    unfold Aset at haA
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp haA
    refine ⟨fun p => f p + e p, fun p => ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      have := (e p).2; have := hf p; nlinarith
    · rw [Finset.prod_insert ha, hprod]
      unfold En
      push_cast
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [pow_add, mul_comm]

lemma card_SP {t B : ℕ} (hB1 : 1 ≤ B) (hB : ∀ p ∈ Q, p ≤ B) :
    (Erdos53.sumsAndProducts (Aset Q t)).card ≤
      ((Aset Q t).card * B ^ (t * Q.card) + 1) + ((Aset Q t).card * t + 1) ^ Q.card := by
  classical
  unfold Erdos53.sumsAndProducts
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · have hsub : ((Aset Q t).powerset.erase ∅).image (fun S => ∑ b ∈ S, b) ⊆
        Finset.Icc (0 : ℤ) (((Aset Q t).card * B ^ (t * Q.card) : ℕ) : ℤ) := by
      intro x hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
      have hS' : S ⊆ Aset Q t := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
      have hb : ∀ b ∈ S, 0 ≤ b ∧ b ≤ ((B ^ (t * Q.card) : ℕ) : ℤ) := by
        intro b hb
        have := hS' hb
        unfold Aset at this
        obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp this
        exact ⟨by positivity, by exact_mod_cast En_le Q hB1 hB e⟩
      rw [Finset.mem_Icc]
      refine ⟨Finset.sum_nonneg fun b hb2 => (hb b hb2).1, ?_⟩
      calc ∑ b ∈ S, b ≤ S.card • ((B ^ (t * Q.card) : ℕ) : ℤ) :=
            Finset.sum_le_card_nsmul _ _ _ fun b hb' => (hb b hb').2
        _ ≤ _ := by
          rw [nsmul_eq_mul]; push_cast
          have := Finset.card_le_card hS'
          have h0 : (0:ℤ) ≤ (B:ℤ) ^ (t * Q.card) := by positivity
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) h0
    calc _ ≤ (Finset.Icc (0 : ℤ) (((Aset Q t).card * B ^ (t * Q.card) : ℕ) : ℤ)).card :=
          Finset.card_le_card hsub
      _ = _ := by rw [Int.card_Icc]; omega
  · set T := (Aset Q t).card * t + 1
    have hsub : ((Aset Q t).powerset.erase ∅).image (fun S => ∏ b ∈ S, b) ⊆
        (Finset.univ : Finset (Q → Fin T)).image
          (fun f => ∏ p : Q, ((p : ℕ) : ℤ) ^ (f p : ℕ)) := by
      intro x hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
      have hS' : S ⊆ Aset Q t := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
      obtain ⟨f, hf, hprod⟩ := prod_form Q S hS'
      refine Finset.mem_image.mpr ⟨fun p => ⟨f p, ?_⟩, Finset.mem_univ _, ?_⟩
      · have h1 := hf p
        have h2 := Finset.card_le_card hS'
        have : S.card * t ≤ (Aset Q t).card * t := Nat.mul_le_mul_right _ h2
        omega
      · rw [hprod]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Q → Fin T)).card := Finset.card_image_le
      _ = T ^ Q.card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

lemma nat_bound (k : ℕ) (hk : 4 ≤ k) :
    (k ^ k * (k ^ 4) ^ (k * k) + 1) + (k ^ k * k + 1) ^ k ≤ k ^ (6 * (k * k)) := by
  have hk1 : 1 ≤ k := by omega
  have hkk : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
  have e1 : k ^ k * (k ^ 4) ^ (k * k) ≤ k ^ (5 * (k * k)) := by
    rw [← pow_mul, ← pow_add]; exact Nat.pow_le_pow_right hk1 (by omega)
  have e2 : k ^ k * k + 1 ≤ k ^ (k + 2) := by
    have : 1 ≤ k ^ k * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [pow_succ, pow_succ]; nlinarith
  have e3 : (k ^ k * k + 1) ^ k ≤ k ^ (5 * (k * k)) := by
    calc (k ^ k * k + 1) ^ k ≤ (k ^ (k + 2)) ^ k := Nat.pow_le_pow_left e2 _
      _ = k ^ ((k + 2) * k) := by rw [pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right hk1 (by nlinarith)
  have e4 : 1 ≤ k ^ (5 * (k * k)) := Nat.one_le_pow _ _ (by omega)
  have e5 : 4 ≤ k ^ (k * k) := by
    calc 4 ≤ k := hk
      _ = k ^ 1 := (pow_one k).symm
      _ ≤ _ := Nat.pow_le_pow_right hk1 (by nlinarith)
  calc _ ≤ 3 * k ^ (5 * (k * k)) := by omega
    _ ≤ k ^ (k * k) * k ^ (5 * (k * k)) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [← pow_add]; ring_nf

lemma real_bound (k : ℕ) (hk : 4 ≤ k) :
    ((k ^ (6 * (k * k)) : ℕ) : ℝ) ≤
      Real.exp (12 * Real.log ((k ^ k : ℕ) : ℝ) ^ 2 / Real.log (Real.log ((k ^ k : ℕ) : ℝ))) := by
  have hk0 : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hlk : 1 < Real.log k := by
    have : Real.log 4 ≤ Real.log k := Real.log_le_log (by norm_num) hk0
    have h4 : (1:ℝ) < Real.log 4 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have hL : Real.log ((k ^ k : ℕ) : ℝ) = k * Real.log k := by push_cast; rw [Real.log_pow]
  set L := (k : ℝ) * Real.log k with hLdef
  have hL1 : 1 < L := by nlinarith
  have hLL0 : 0 < Real.log L := Real.log_pos hL1
  have hLL : Real.log L ≤ 2 * Real.log k := by
    have : L ≤ (k : ℝ) ^ 2 := by
      have := Real.log_le_sub_one_of_pos hkpos
      rw [hLdef, sq]; exact mul_le_mul_of_nonneg_left (by linarith) hkpos.le
    calc Real.log L ≤ Real.log ((k:ℝ) ^ 2) := Real.log_le_log (by linarith) this
      _ = 2 * Real.log k := by rw [Real.log_pow]; push_cast; ring
  rw [hL]
  have lhs : ((k ^ (6 * (k * k)) : ℕ) : ℝ) = Real.exp (6 * (k * k) * Real.log k) := by
    rw [Nat.cast_pow]
    conv_lhs => rw [← Real.exp_log hkpos]
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [lhs, Real.exp_le_exp, le_div_iff₀ hLL0]
  have hlog0 : 0 < Real.log k := by linarith
  calc 6 * (k * k) * Real.log k * Real.log L ≤ 6 * (k * k) * Real.log k * (2 * Real.log k) := by
        apply mul_le_mul_of_nonneg_left hLL; positivity
    _ = 12 * L ^ 2 := by rw [hLdef]; ring

end

end OMA53

theorem OMA.solution : type_of% @Erdos53.erdos_53.variants.upper := by
  open OMA53 in
  refine ⟨12, by norm_num, fun N => ?_⟩
  set j := N + 2
  set Q := (Finset.range (16 ^ j + 1)).filter Nat.Prime
  set k := Q.card
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hkpi : k = Nat.primeCounting (16 ^ j) := by
    simp only [k, Q]
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hk2 : 2 ^ j ≤ k := hkpi ▸ pi_big j (by omega)
  have h4 : 4 ≤ k := by
    have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hB : ∀ p ∈ Q, p ≤ k ^ 4 := by
    intro p hp
    have h1 : p ≤ 16 ^ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    calc p ≤ 16 ^ j := h1
      _ = (2 ^ j) ^ 4 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ k ^ 4 := Nat.pow_le_pow_left hk2 4
  have hB1 : 1 ≤ k ^ 4 := Nat.one_le_pow _ _ (by omega)
  refine ⟨Aset Q k, ?_, ?_⟩
  · rw [Aset_card Q hQ]
    have hN : N ≤ 16 ^ j := by
      have : N < 2 ^ N := Nat.lt_two_pow_self
      have : 2 ^ N ≤ 16 ^ j := (Nat.pow_le_pow_left (by norm_num) N).trans
        (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    calc N ≤ 16 ^ j := hN
      _ = (2 ^ j) ^ 4 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ k ^ 4 := Nat.pow_le_pow_left hk2 4
      _ ≤ k ^ k := Nat.pow_le_pow_right (by omega) h4
  · have hc := card_SP Q (t := k) hB1 hB
    rw [Aset_card Q hQ] at hc ⊢
    have hn := nat_bound k h4
    have : (Erdos53.sumsAndProducts (Aset Q k)).card ≤ k ^ (6 * (k * k)) := hc.trans hn
    calc ((Erdos53.sumsAndProducts (Aset Q k)).card : ℝ) ≤ ((k ^ (6 * (k * k)) : ℕ) : ℝ) := by
          exact_mod_cast this
      _ ≤ _ := real_bound k h4
