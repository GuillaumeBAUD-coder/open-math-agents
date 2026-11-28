import OMAStatements.S_itp_relay_channel

/-!
# A two-use disproof for the three-constraint relay rate

The physical channel K has source (B,M), relay input R, destination (B+R,M+N),
and relay observation (B,N). The first sum is integer addition and the second is
addition of bits with an independent fair mask N. L is a finite memoryless channel
whose relay alphabet consists of four two-use strategies. Its second input can
depend on the first observed source bit.

The four-strategy witness embeds in BK, the channel allowing all 32 causal policies.
The proof establishes T₇(K) = 3/2 and T₇(BK) > 3. It then runs every code for BK
over K in consecutive pairs, preserving its average error. Padding and message
restriction implement the floor convention at every sufficiently large length.
Applying the proposed universal equality to K and BK yields a contradiction.
-/

/-! Scalar entropy inequalities for the masked binary-adder relay counterexample.
All entropies in the analytic lemmas are in nats. -/

namespace RelayAdderCertificate
open Real

/-- A pointwise form of the cross-entropy bound, valid for zero observed mass. -/
private lemma cross_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    negMulLog x ≤ -x * log y + y - x := by
  by_cases h : x = 0
  · simp [h, hy.le]
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
  have hh := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hy hx')) hx
  rw [log_div hy.ne' h, mul_sub, mul_sub, mul_div_cancel₀ _ h, mul_one] at hh
  unfold negMulLog
  linarith

/-- A quantitative bound below the maximum of binary entropy. -/
private lemma binary_bound (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    binEntropy t ≤ log 2 + t * (1 - t) - 1 / 4 := by
  let a := sqrt t
  let b := sqrt (1 - t)
  have ha : 0 < a := Real.sqrt_pos.2 ht
  have hb : 0 < b := Real.sqrt_pos.2 (sub_pos.2 ht')
  have hab : 0 < a + b := add_pos ha hb
  have h1 := cross_bound t (a / (a+b)) ht.le (div_pos ha hab)
  have h2 := cross_bound (1-t) (b / (a+b)) (by linarith) (div_pos hb hab)
  rw [log_div ha.ne' hab.ne', show log a = log t / 2 from log_sqrt ht.le] at h1
  rw [log_div hb.ne' hab.ne', show log b = log (1-t) / 2 from log_sqrt (by linarith)] at h2
  have hmass : a/(a+b) + b/(a+b) = 1 := by rw [← add_div, div_self hab.ne']
  have hent : binEntropy t ≤ 2 * log (a+b) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    unfold negMulLog at *
    linarith
  have hlog := log_le_sub_one_of_pos (show 0 < (a+b)^2 / 2 by positivity)
  rw [log_div (by positivity) (by norm_num), log_pow] at hlog
  have ha2 : a^2 = t := sq_sqrt ht.le
  have hb2 : b^2 = 1-t := sq_sqrt (by linarith)
  have hab2 : (a*b)^2 = t*(1-t) := by rw [mul_pow,ha2,hb2]
  nlinarith [sq_nonneg (a*b-1/2)]

/-- Entropy of the ordinary sum of two independent bits of arbitrary biases. -/
theorem independent_adder_entropy (p q : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hq : 0 ≤ q) (hq' : q ≤ 1) :
    negMulLog ((1-p)*(1-q)) + negMulLog (p*(1-q)+(1-p)*q) + negMulLog (p*q)
      ≤ 3 / 2 * log 2 := by
  let t := (p+q)/2
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hlt : 0 < log 2 := log_pos (by norm_num)
  rcases eq_or_lt_of_le ht0 with hz | ht
  · have hpz : p=0 := by dsimp [t] at hz; linarith
    have hqz : q=0 := by dsimp [t] at hz; linarith
    simp [hpz,hqz]; linarith
  rcases eq_or_lt_of_le ht1 with ho | ht'
  · have hpo : p=1 := by dsimp [t] at ho; linarith
    have hqo : q=1 := by dsimp [t] at ho; linarith
    simp [hpo,hqo]; linarith
  have hs : 0 < 1-t := sub_pos.mpr ht'
  let a := (1-p)*(1-q)
  let b := p*(1-q)+(1-p)*q
  let c := p*q
  have h0 := cross_bound a ((1-t)^2) (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have h1 := cross_bound b (2*t*(1-t))
    (add_nonneg (mul_nonneg hp (by linarith)) (mul_nonneg (by linarith) hq)) (by positivity)
  have h2 := cross_bound c (t^2) (mul_nonneg hp hq) (by positivity)
  rw [log_pow] at h0 h2
  rw [log_mul (by positivity) hs.ne', log_mul (by norm_num) ht.ne'] at h1
  have hc : negMulLog a + negMulLog b + negMulLog c ≤ 2*binEntropy t - b*log 2 := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog] at h0 h1 h2 ⊢
    dsimp [a,b,c,t] at *
    linarith only [h0,h1,h2]
  have hw : 2*t*(1-t) ≤ b := by dsimp [t,b]; nlinarith [sq_nonneg (p-q)]
  have hvar : 0 ≤ 1/4 - t*(1-t) := by nlinarith [sq_nonneg (t-1/2)]
  have hlog : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hproduct := mul_nonneg hvar (sub_nonneg.mpr hlog)
  change negMulLog a + negMulLog b + negMulLog c ≤ _
  nlinarith only [hc,binary_bound t ht ht',mul_le_mul_of_nonneg_right hw hlt.le,hproduct]

/-- Strict separation in bits follows from an integer comparison. -/
theorem strict_gap : (3 : ℝ) < 11/6 + 3/4 * logb 2 3 := by
  have h : (2 : ℝ)^14 < 3^9 := by norm_num
  have hh := log_lt_log (by positivity) h
  rw [log_pow, log_pow] at hh
  have hp : 0 < log 2 := log_pos (by norm_num)
  norm_num at hh
  unfold logb
  field_simp
  linarith only [hh]


open OMA.S_itp_relay_channel

abbrev Bit := Fin 2
abbrev Observation := Bit × Bit

def integerSum (b r : Bit) : Fin 3 := ⟨b.val + r.val, by omega⟩

def secondInput (firstRelay coin : Bit) (observation : Observation) : Bit :=
  if observation.1 ≠ firstRelay then observation.1 else coin

def massMatrix : Fin 3 → Fin 3 → ℕ := ![![2,3,1], ![4,4,4], ![1,3,2]]

/-- Entropy of the actual ternary outputs in the catalogue's bit units. -/
theorem sumPair_entropy :
    ent (fun o : Fin 3 × Fin 3 => (massMatrix o.1 o.2 : ℝ) / 24) = 11/6 + 3/4 * logb 2 3 := by
  simp only [ent, Fintype.sum_prod_type, Fin.sum_univ_succ, massMatrix]
  norm_num [Real.negMulLog, Real.logb, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  have l24 : log 24 = 3 * log 2 + log 3 := by
    rw [show (24 : ℝ) = 2^3 * 3 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  have l12 : log 12 = 2 * log 2 + log 3 := by
    rw [show (12 : ℝ) = 2^2 * 3 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  have l8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, log_pow]
    norm_num
  have l6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  simp only [one_div, Real.log_inv, l6, l8, l12, l24]
  field_simp [show log 2 ≠ 0 from (log_pos (by norm_num)).ne']
  ring

/-- The one-use adder bound in the entropy convention of the catalogue problem. -/
theorem independent_adder_entropy_bits (p q : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hq : 0 ≤ q) (hq' : q ≤ 1) :
    ent ![(1-p)*(1-q), p*(1-q)+(1-p)*q, p*q] ≤ 3/2 := by
  simp [ent, Fin.sum_univ_succ]
  rw [← add_div, ← add_div]
  apply (div_le_iff₀ (log_pos (by norm_num : (1:ℝ) < 2))).mpr
  linarith only [independent_adder_entropy p q hp hp' hq hq']

end RelayAdderCertificate

/-! Finite pushforward and entropy identities in the conventions of the relay catalogue. -/
namespace RelayEntropy
open OMA.S_itp_relay_channel
open scoped BigOperators Classical

variable {Ω X Y Z W : Type} [Fintype Ω] [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]

noncomputable def H (p : Ω → ℝ) (f : Ω → X) := ent (push f p)

lemma sum_push (p : Ω → ℝ) (f : Ω → X) (g : X → ℝ) :
    ∑ x, push f p x * g x = ∑ i, p i * g (f i) := by
  simp only [push, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

omit [Fintype Y] in
lemma push_push (p : Ω → ℝ) (f : Ω → X) (g : X → Y) :
    push g (push f p) = push (fun i => g (f i)) p := by
  funext y
  calc
    _ = ∑ x, push f p x * (if g x = y then 1 else 0) := by simp [push, mul_ite]
    _ = _ := by rw [sum_push]; simp [push, mul_ite]

lemma H_push (p : Ω → ℝ) (f : Ω → X) (g : X → Y) :
    H (push f p) g = H p (fun i => g (f i)) := by simp [H,push_push]

lemma H_fibres (p : Ω → ℝ) (f : Ω → X) :
    H p f = ∑ i, p i * (-Real.log (push f p (f i)) / Real.log 2) := by
  rw [← sum_push p f (fun x => -Real.log (push f p x) / Real.log 2)]
  unfold H ent
  apply Finset.sum_congr rfl
  intro x _
  unfold Real.negMulLog
  ring

lemma H_partition (p : Ω → ℝ) (f : Ω → X) (g : Ω → Y)
    (h : ∀ i j, f i = f j ↔ g i = g j) : H p f = H p g := by
  simp only [H_fibres, push, h]

lemma cmi_push (p : Ω → ℝ) (f : Ω → X) (g : Ω → Y) (h : Ω → Z) :
    cmi (push (fun i => (f i,g i,h i)) p) =
    H p (fun i => (f i,h i)) + H p (fun i => (g i,h i))
      - H p (fun i => (f i,g i,h i)) - H p h := by
  simp only [cmi, push_push, H]

lemma push_id (p : X → ℝ) : push id p = p := by ext; simp [push]

lemma entropy_bind (p : X → ℝ) (k : X → Y → ℝ) (hk : ∀ x, ∑ y, k x y = 1) :
    ent (fun xy : X × Y => p xy.1 * k xy.1 xy.2) = ent p + ∑ x, p x * ent (k x) := by
  simp only [ent, Fintype.sum_prod_type, Real.negMulLog_mul, add_div, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    simp_rw [mul_div_assoc]
    rw [← Finset.sum_mul,hk,one_mul]
  · apply Finset.sum_congr rfl
    intro x _
    simp [Finset.mul_sum, mul_div_assoc]

lemma push_total (p : Ω → ℝ) (f : Ω → X) : ∑ x, push f p x = ∑ i, p i := by
  simpa using sum_push p f (fun _ => 1)

/-- A normalized next-step kernel appends its mean entropy to the entropy of the prefix. -/
lemma H_extend (p : Ω → ℝ) (f : Ω → X) (g : Ω → Y) (k : X → Y → ℝ)
    (hk : ∀ x, ∑ y, k x y = 1)
    (h : ∀ x y, push (fun i => (f i,g i)) p (x,y) = push f p x * k x y) :
    H p (fun i => (f i,g i)) = H p f + ∑ x, push f p x * ent (k x) := by
  have he : push (fun i => (f i,g i)) p = fun xy => push f p xy.1 * k xy.1 xy.2 :=
    funext fun ⟨x,y⟩ => h x y
  rw [H, he, entropy_bind _ _ hk, H]

end RelayEntropy

namespace RelayEntropy
open OMA.S_itp_relay_channel
open scoped BigOperators Classical
variable {Ω X Y Z : Type} [Fintype Ω] [Fintype X] [Fintype Y] [Fintype Z]

noncomputable def extend (p : Ω → ℝ) (k : Ω → X → ℝ) (t : Ω × X) := p t.1 * k t.1 t.2
noncomputable def CE (p : Ω → ℝ) (x : Ω → X) (g : Ω → Y) :=
  H p (fun i => (g i,x i)) - H p g
noncomputable def MI (p : Ω → ℝ) (x : Ω → X) (y : Ω → Y) (g : Ω → Z) :=
  cmi (push (fun i => (x i,y i,g i)) p)

lemma MI_eq (p : Ω → ℝ) (x : Ω → X) (y : Ω → Y) (g : Ω → Z) :
    MI p x y g = CE p y g - CE p y (fun i => (g i,x i)) := by
  rw [MI,cmi_push,CE,CE]
  have h1 := H_partition p (fun i => (x i,g i)) (fun i => (g i,x i))
    (fun i j => by simp only [Prod.mk.injEq]; tauto)
  have h2 := H_partition p (fun i => (y i,g i)) (fun i => (g i,y i))
    (fun i j => by simp only [Prod.mk.injEq]; tauto)
  have h3 := H_partition p (fun i => (x i,y i,g i)) (fun i => ((g i,x i),y i))
    (fun i j => by simp only [Prod.mk.injEq]; tauto)
  linarith

lemma CE_context {W : Type} [Fintype W] (p : Ω → ℝ) (x : Ω → X)
    (f : Ω → Y) (g : Ω → W) (h : ∀ i j, f i = f j ↔ g i = g j) :
    CE p x f = CE p x g := by
  unfold CE
  rw [H_partition p (fun i => (f i,x i)) (fun i => (g i,x i))
    (fun i j => by simp only [Prod.mk.injEq,h]), H_partition p f g h]

lemma CE_determined (p : Ω → ℝ) (x : Ω → X) (f : Ω → Y)
    (h : ∀ i j, f i = f j → x i = x j) : CE p x f = 0 := by
  unfold CE
  rw [H_partition p _ f (fun i j => by simp only [Prod.mk.injEq]; exact ⟨And.left,fun h' => ⟨h',h i j h'⟩⟩)]
  exact sub_self _

lemma CE_chain (p : Ω → ℝ) (x : Ω → X) (y : Ω → Y) (g : Ω → Z) :
    CE p (fun i => (x i,y i)) g = CE p x g + CE p y (fun i => (g i,x i)) := by
  unfold CE
  rw [H_partition p (fun i => (g i,x i,y i)) (fun i => ((g i,x i),y i))
    (fun i j => by simp only [Prod.mk.injEq]; tauto)]
  ring

omit [Fintype Y] in
lemma push_extend (p : Ω → ℝ) (k : Ω → X → ℝ) (hk : ∀ i, ∑ x, k i x = 1) (f : Ω → Y) :
    push (fun t : Ω × X => f t.1) (extend p k) = push f p := by
  funext y
  simp only [push, extend, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f i = y <;> simp [hi,← Finset.mul_sum,hk]

lemma CE_drop (p : Ω → ℝ) (k : Ω → X → ℝ) (hk : ∀ i, ∑ x, k i x = 1)
    (y : Ω → Y) (g : Ω → Z) :
    CE (extend p k) (fun t => y t.1) (fun t => g t.1) = CE p y g := by
  unfold CE H
  rw [push_extend p k hk (fun i => (g i, y i)),push_extend p k hk]

lemma CE_next (p : Ω → ℝ) (k : Ω → X → ℝ) (hk : ∀ i, ∑ x, k i x = 1)
    (g : Ω → Y) (f : Ω → X → Z) (l : Y → Z → ℝ)
    (hl : ∀ y, ∑ z, l y z = 1) (h : ∀ i, push (f i) (k i) = l (g i)) :
    CE (extend p k) (fun t => f t.1 t.2) (fun t => g t.1) = ∑ i, p i * ent (l (g i)) := by
  unfold CE
  rw [H_extend _ _ _ l hl]
  · rw [add_sub_cancel_left, push_extend p k hk, sum_push]
  · intro y z
    rw [push_extend p k hk]
    simp only [push, extend, Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : g i = y
    · simp only [Prod.mk.injEq,hi,true_and,ite_true]
      -- Pull the fixed prefix mass outside this fibre.
      calc
        _ = p i * push (f i) (k i) z := by
          simp only [push,Finset.mul_sum,mul_ite,mul_zero]
        _ = _ := by rw [h,hi]
    · simp [hi]

end RelayEntropy

namespace RelayEntropy
open OMA.S_itp_relay_channel
open scoped BigOperators Classical
variable {Ω Q A U X R Y Z V : Type} [Fintype Ω] [Fintype Q] [Fintype A] [Fintype U]
  [Fintype X] [Fintype R] [Fintype Y] [Fintype Z] [Fintype V]

abbrev Constraints := ℝ × ℝ × ℝ

def minimum (c : Constraints) := min c.1 (min c.2.1 c.2.2)

noncomputable def three (p : Ω → ℝ) (q : Ω → Q) (a : Ω → A) (u : Ω → U) (x : Ω → X)
    (r : Ω → R) (y : Ω → Y) (z : Ω → Z) (v : Ω → V) : Constraints :=
    let c₁ := MI p (fun i => (x i,r i)) y q - MI p z v (fun i => (u i,x i,r i,y i,q i))
    let c₂ := MI p x (fun i => (v i,y i)) (fun i => (u i,r i,q i)) +
      MI p u z (fun i => (a i,r i,q i))
    let c₃ := c₂ + MI p r y (fun i => (a i,q i)) - MI p z v (fun i => (u i,r i,y i,q i))
    (c₁,c₂,c₃)

noncomputable def rowThree (p : Q × A × U × X × R × Y × Z × V → ℝ) : Constraints :=
  three p Prod.fst (fun t => t.2.1) (fun t => t.2.2.1) (fun t => t.2.2.2.1)
    (fun t => t.2.2.2.2.1) (fun t => t.2.2.2.2.2.1) (fun t => t.2.2.2.2.2.2.1)
    (fun t => t.2.2.2.2.2.2.2)

lemma catalogue_minimum (p : Q × A × U × X × R × Y × Z × V → ℝ) :
    thm7MinRate p = minimum (rowThree p) := rfl

lemma three_push (p : Ω → ℝ) (q : Ω → Q) (a : Ω → A) (u : Ω → U) (x : Ω → X)
    (r : Ω → R) (y : Ω → Y) (z : Ω → Z) (v : Ω → V) :
    rowThree (push (fun i => (q i,a i,u i,x i,r i,y i,z i,v i)) p) =
      three p q a u x r y z v := by
  simp only [rowThree,three,MI,push_push]

lemma CE_swap_chain (p : Ω → ℝ) (v : Ω → V) (y : Ω → Y) (g : Ω → Q) :
    CE p (fun i => (v i,y i)) g = CE p y g + CE p v (fun i => (g i,y i)) := by
  rw [← CE_chain]
  unfold CE
  rw [H_partition p (fun i => (g i,v i,y i)) (fun i => (g i,y i,v i))
    (fun i j => by simp only [Prod.mk.injEq]; tauto)]

/-- Recoverability of the two descriptions cancels the compression term for
    every compressor. This includes stochastic compressors. -/
lemma recoverable_constraints (p : Ω → ℝ) (q : Ω → Q) (a : Ω → A) (u : Ω → U)
    (x : Ω → X) (r : Ω → R) (y : Ω → Y) (z : Ω → Z) (v : Ω → V)
    (recov : ∀ i j, r i = r j → y i = y j → (x i = x j ↔ z i = z j)) :
    let margin := MI p z v (fun i => (u i,r i,y i,q i))
    let dest := MI p (fun i => (x i,r i)) y q
    let source := MI p x y (fun i => (u i,r i,q i)) + MI p u z (fun i => (a i,r i,q i))
    let link := MI p r y (fun i => (a i,q i))
    rowThree (push (fun i => (q i,a i,u i,x i,r i,y i,z i,v i)) p) =
    (dest,source + margin,source + link) := by
  dsimp only
  rw [three_push]
  unfold three
  dsimp only
  have penalty : MI p z v (fun i => (u i,x i,r i,y i,q i)) = 0 := by
    rw [MI_eq,sub_eq_zero]
    apply CE_context
    intro i j
    simp only [Prod.mk.injEq]
    have h := recov i j
    tauto
  have gain : MI p x (fun i => (v i,y i)) (fun i => (u i,r i,q i)) =
      MI p x y (fun i => (u i,r i,q i)) + MI p z v (fun i => (u i,r i,y i,q i)) := by
    rw [MI_eq,MI_eq,MI_eq,CE_swap_chain,CE_swap_chain]
    have h1 := CE_context p v (fun i => ((u i,r i,q i),y i)) (fun i => (u i,r i,y i,q i))
      (fun i j => by simp only [Prod.mk.injEq]; tauto)
    have h2 := CE_context p v (fun i => (((u i,r i,q i),x i),y i))
      (fun i => ((u i,r i,y i,q i),z i)) (fun i j => by
        simp only [Prod.mk.injEq]
        have h := recov i j
        tauto)
    linarith
  rw [penalty,sub_zero,gain]
  congr 2 <;> ring

end RelayEntropy

namespace RelayMaskedLaw
open OMA.S_itp_relay_channel RelayEntropy
open scoped BigOperators Classical

abbrev Prefix (Q A U R : Type) := ((Q × A) × U) × R
abbrev Base (Q A U R X : Type) := Prefix Q A U R × X
abbrev Sample (Q A U R X N V : Type) := (Base Q A U R X × N) × V
abbrev Row (Q A U X R Y Z V : Type) := Q × A × U × X × R × Y × Z × V

variable {Q A U X R Y Z N V : Type} [Fintype Q] [Fintype A] [Fintype U] [Fintype X]
  [Fintype R] [Fintype Y] [Fintype Z] [Fintype N] [Fintype V]

noncomputable def prefixLaw (pq : Q → ℝ) (pa : Q → A → ℝ) (pu : A × Q → U → ℝ)
    (pr : A × Q → R → ℝ) (i : Prefix Q A U R) :=
  pq i.1.1.1 * pa i.1.1.1 i.1.1.2 * pu (i.1.1.2,i.1.1.1) i.1.2 * pr (i.1.1.2,i.1.1.1) i.2

noncomputable def baseLaw (pq : Q → ℝ) (pa : Q → A → ℝ) (pu : A × Q → U → ℝ)
    (px : U × Q → X → ℝ) (pr : A × Q → R → ℝ) :=
  extend (prefixLaw pq pa pu pr) (fun i => px (i.1.2,i.1.1.1))

def pack (out : X → R → N → Y × Z) (s : Sample Q A U R X N V) : Row Q A U X R Y Z V :=
  let i := s.1.1.1
  let x := s.1.1.2
  let o := out x i.2 s.1.2
  (i.1.1.1,i.1.1.2,i.1.2,x,i.2,o.1,o.2,s.2)

noncomputable def sampleLaw (out : X → R → N → Y × Z) (noise : N → ℝ)
    (p : Base Q A U R X → ℝ) (pv : U × R × Z × Q → V → ℝ) :=
  extend (extend p (fun _ => noise)) (fun j =>
    let i := j.1.1
    pv (i.1.2,i.2,(out j.1.2 i.2 j.2).2,i.1.1.1))

set_option maxHeartbeats 1200000 in
/-- Exact equality of the catalogue joint mass function with the distribution
    obtained by sampling the noise and then the compression kernel. -/
lemma joint_sample (out : X → R → N → Y × Z) (noise : N → ℝ)
    (pq : Q → ℝ) (pa : Q → A → ℝ) (pu : A × Q → U → ℝ)
    (px : U × Q → X → ℝ) (pr : A × Q → R → ℝ) (pv : U × R × Z × Q → V → ℝ) :
    thm7Joint (fun i => push (out i.1 i.2) noise) pq pa pu px pr pv =
    push (pack out) (sampleLaw out noise (baseLaw pq pa pu px pr) pv) := by
  let J := thm7Joint (fun i => push (out i.1 i.2) noise) pq pa pu px pr pv
  let μ := sampleLaw out noise (baseLaw pq pa pu px pr) pv
  have expect (g : Row Q A U X R Y Z V → ℝ) :
      ∑ i, J i * g i = ∑ i, μ i * g (pack out i) := by
    simp only [J,μ, thm7Joint, Fintype.sum_prod_type, pack, sampleLaw, extend,baseLaw,prefixLaw]
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro x _
    have h := sum_push noise (out x r) (fun o => ∑ v, pq q * pa q a * pu (a,q) u *
      pr (a,q) r * px (u,q) x * pv (u,r,o.2,q) v * g (q,a,u,x,r,o.1,o.2,v))
    simp only [Fintype.sum_prod_type, Finset.mul_sum] at h
    refine Eq.trans ?_ (h.trans ?_)
    · apply Finset.sum_congr rfl; intro y _
      apply Finset.sum_congr rfl; intro z _
      apply Finset.sum_congr rfl; intro v _
      ac_rfl
    · apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro v _
      ac_rfl
  funext t
  have h := expect (fun s => if s = t then 1 else 0)
  simp [mul_ite] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  by_cases he : pack out i = t <;> simp [he,μ]

lemma base_total (pq : Q → ℝ) (pa : Q → A → ℝ) (pu : A × Q → U → ℝ)
    (px : U × Q → X → ℝ) (pr : A × Q → R → ℝ)
    (hq : IsPmf pq) (ha : IsKernel pa) (hu : IsKernel pu) (hx : IsKernel px)
    (hr : IsKernel pr) : ∑ i, baseLaw pq pa pu px pr i = 1 := by
  simp [baseLaw, extend, prefixLaw, Fintype.sum_prod_type,← Finset.mul_sum,
    hx.2, hr.2, hu.2, ha.2, hq.2]

section Noise
variable {Ω B C G E : Type} [Fintype Ω] [Fintype B] [Fintype C] [Fintype G] [Fintype E]

noncomputable def uniform (G : Type) [Fintype G] (_ : G) : ℝ := (Fintype.card G : ℝ)⁻¹

lemma uniform_total [Nonempty G] : ∑ n : G, uniform G n = 1 := by
  simp [uniform, Fintype.card_ne_zero]

lemma uniform_perm (e : G ≃ G) : push e (uniform G) = uniform G := by
  funext n
  simp [push,uniform,← e.eq_symm_apply]

/-- A fresh uniform coordinate, permuted by the past, adds the same entropy for
    every conditioning variable measured before that coordinate. -/
lemma masked_CE (p : Ω → ℝ) (hp : ∑ i, p i = 1) [Nonempty G]
    (kv : Ω × G → V → ℝ) (hv : IsKernel kv) (t : Ω → B) (ctx : Ω → C)
    (perm : Ω → G ≃ G) :
    CE (extend (extend p (fun _ => uniform G)) kv)
      (fun s => (t s.1.1,perm s.1.1 s.1.2)) (fun s => ctx s.1.1) =
    CE p t ctx + ent (uniform G) := by
  rw [CE_drop _ kv hv.2 (fun j => (t j.1,perm j.1 j.2)) (fun j => ctx j.1)]
  rw [CE_chain, CE_drop _ _ (fun _ => uniform_total) t ctx,
    CE_next p (fun _ => uniform G) (fun _ => uniform_total) (fun i => (ctx i,t i))
      (fun i => (perm i : G → G)) (fun _ => uniform G) (fun _ => uniform_total)
      (fun i => uniform_perm (perm i))]
  rw [← Finset.sum_mul,hp,one_mul]

lemma masked_MI (p : Ω → ℝ) (hp : ∑ i, p i = 1) [Nonempty G]
    (kv : Ω × G → V → ℝ) (hv : IsKernel kv) (e : Ω → E) (t : Ω → B) (ctx : Ω → C)
    (perm : Ω → G ≃ G) :
    MI (extend (extend p (fun _ => uniform G)) kv)
      (fun s => e s.1.1) (fun s => (t s.1.1,perm s.1.1 s.1.2)) (fun s => ctx s.1.1) =
    MI p e t ctx := by
  rw [MI_eq, MI_eq, masked_CE p hp kv hv t ctx perm,
    masked_CE p hp kv hv t (fun i => (ctx i,e i)) perm]
  ring

end Noise
end RelayMaskedLaw

namespace RelayMaskedLaw
open OMA.S_itp_relay_channel RelayEntropy
open scoped BigOperators Classical
variable {Q A U B R T G V : Type}
variable [Fintype Q] [Fintype A] [Fintype U] [Fintype B] [Fintype R] [Fintype T]
  [Fintype G] [Fintype V] [AddGroup G]

abbrev State (Q A U B G R : Type) := Base Q A U R (B × G)

def baseQ (i : State Q A U B G R) := i.1.1.1.1
def baseA (i : State Q A U B G R) := i.1.1.1.2
def baseU (i : State Q A U B G R) := i.1.1.2
def baseR (i : State Q A U B G R) := i.1.2
def baseX (i : State Q A U B G R) := i.2

def maskedOut (adder : B → R → T) (x : B × G) (r : R) (n : G) :=
  ((adder x.1 r,x.2+n),(x.1,n))

noncomputable def maskedK (adder : B → R → T) (i : (B × G) × R) :=
  push (maskedOut adder i.1 i.2) (uniform G)

omit [AddGroup G] in
lemma source_markov (pq : Q → ℝ) (pa : Q → A → ℝ) (pu : A × Q → U → ℝ)
    (px : U × Q → B × G → ℝ) (pr : A × Q → R → ℝ) (hx : IsKernel px) :
    let p := baseLaw pq pa pu px pr
    CE p (fun i => (baseX i).1) (fun i => (baseU i,baseR i,baseQ i)) =
    CE p (fun i => (baseX i).1) (fun i => ((baseA i,baseR i,baseQ i),baseU i)) := by
  let l (uq : U × Q) := push Prod.fst (px uq)
  have hl (uq) : ∑ b, l uq b = 1 := (push_total _ _).trans (hx.2 _)
  dsimp only
  unfold baseLaw baseX baseU baseR baseQ baseA
  rw [CE_next _ _ (fun i => hx.2 _) (fun i : Prefix Q A U R => (i.1.2,i.2,i.1.1.1))
    (fun _ x => x.1) (fun c => l (c.1,c.2.2)) (fun c => hl _) (fun _ => rfl)]
  rw [CE_next _ _ (fun i => hx.2 _) (fun i : Prefix Q A U R => ((i.1.1.2,i.2,i.1.1.1),i.1.2))
    (fun _ x => x.1) (fun c => l (c.2,c.1.2.2)) (fun c => hl _) (fun _ => rfl)]

section
variable {Ω C : Type} [Fintype Ω] [Fintype C]

omit [Fintype R] in
lemma CE_recover_adder (p : Ω → ℝ) (b : Ω → B) (r : Ω → R) (c : Ω → C)
    (adder : B → R → T) (hinj : ∀ r, Function.Injective (fun b => adder b r))
    (hc : ∀ i j, c i = c j → r i = r j) :
    CE p (fun i => adder (b i) (r i)) c = CE p b c := by
  unfold CE
  congr 1
  apply H_partition
  intro i j
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h,e⟩
    rw [hc i j h] at e
    exact ⟨h,hinj _ e⟩
  · rintro ⟨h,e⟩
    exact ⟨h,by rw [e,hc i j h]⟩
end

omit [Fintype B] [Fintype G] in
/-- Once the masked destination components agree, equality of source inputs
    is equivalent to equality of relay observations. -/
lemma masked_recovery {x x' : B × G} {n n' : G} (hm : x.2 + n = x'.2 + n') :
    x = x' ↔ (x.1,n) = (x'.1,n') := by
  constructor
  · rintro rfl
    exact Prod.ext rfl (add_left_cancel hm)
  · intro h
    obtain ⟨hb,rfl⟩ := Prod.mk.inj h
    exact Prod.ext hb (add_right_cancel hm)

set_option maxHeartbeats 1500000 in
theorem masked_constraints (adder : B → R → T) (hinj : ∀ r, Function.Injective (fun b => adder b r))
    (pq : Q → ℝ) (pa : Q → A → ℝ) (pu : A × Q → U → ℝ)
    (px : U × Q → B × G → ℝ) (pr : A × Q → R → ℝ)
    (pv : U × R × (B × G) × Q → V → ℝ)
    (hq : IsPmf pq) (ha : IsKernel pa) (hu : IsKernel pu)
    (hx : IsKernel px) (hr : IsKernel pr) (hV : IsKernel pv) :
    let p := baseLaw pq pa pu px pr
    let t (i : State Q A U B G R) := adder (baseX i).1 (baseR i)
    let μ := sampleLaw (maskedOut adder) (uniform G) p pv
    let margin := MI μ (fun s => ((baseX s.1.1).1,s.1.2)) Prod.snd
      (fun s => (baseU s.1.1,baseR s.1.1,(t s.1.1,(baseX s.1.1).2+s.1.2),baseQ s.1.1))
    rowThree (thm7Joint (maskedK adder) pq pa pu px pr pv) =
    (CE p t baseQ,CE p t (fun i => (baseA i,baseR i,baseQ i)) + margin,
      CE p t (fun i => (baseA i,baseQ i))) := by
  dsimp only
  let p := baseLaw pq pa pu px pr
  let t (i : State Q A U B G R) := adder (baseX i).1 (baseR i)
  let b (i : State Q A U B G R) := (baseX i).1
  let m (i : State Q A U B G R) := (baseX i).2
  let k (j : State Q A U B G R × G) := pv (baseU j.1,baseR j.1,(b j.1,j.2),baseQ j.1)
  let μ := extend (extend p (fun _ => uniform G)) k
  have hp : ∑ i, p i = 1 := base_total _ _ _ _ _ hq ha hu hx hr
  have hk : IsKernel k := ⟨fun i v => hV.1 _ _, fun i => hV.2 _⟩
  let y (s : (State Q A U B G R × G) × V) := (t s.1.1,m s.1.1+s.1.2)
  let z (s : (State Q A U B G R × G) × V) := (b s.1.1,s.1.2)
  let margin := MI μ z Prod.snd (fun s => (baseU s.1.1,baseR s.1.1,y s,baseQ s.1.1))
  have recov (i j : (State Q A U B G R × G) × V) (_ : baseR i.1.1 = baseR j.1.1)
      (ey : y i = y j) : baseX i.1.1 = baseX j.1.1 ↔ z i = z j := by
    exact masked_recovery (congrArg Prod.snd ey)
  have red := recoverable_constraints μ (fun s => baseQ s.1.1) (fun s => baseA s.1.1)
    (fun s => baseU s.1.1) (fun s => baseX s.1.1) (fun s => baseR s.1.1) y z Prod.snd recov
  rw [show thm7Joint (maskedK adder) pq pa pu px pr pv = _ from joint_sample (maskedOut adder) (uniform G) pq pa pu px pr pv]
  refine red.trans ?_
  have my {E C : Type} [Fintype E] [Fintype C] (e : State Q A U B G R → E) (c : State Q A U B G R → C) :
      MI μ (fun s => e s.1.1) y (fun s => c s.1.1) = MI p e t c :=
    masked_MI p hp k hk e t c (fun i => Equiv.addLeft (m i))
  have mz {E C : Type} [Fintype E] [Fintype C] (e : State Q A U B G R → E) (c : State Q A U B G R → C) :
      MI μ (fun s => e s.1.1) z (fun s => c s.1.1) = MI p e b c :=
    masked_MI p hp k hk e b c (fun _ => Equiv.refl G)
  rw [my (fun i => (baseX i,baseR i)) baseQ,
    my baseX (fun i => (baseU i,baseR i,baseQ i)),
    mz baseU (fun i => (baseA i,baseR i,baseQ i)),my baseR (fun i => (baseA i,baseQ i))]
  have dst : MI p (fun i => (baseX i,baseR i)) t baseQ = CE p t baseQ := by
    rw [MI_eq,CE_determined p t (fun i => (baseQ i,baseX i,baseR i)),sub_zero]
    intro i j h
    change adder _ _ = adder _ _
    rw [show baseX i = baseX j from congrArg (fun s => s.2.1) h,
      show baseR i = baseR j from congrArg (fun s => s.2.2) h]
  have src : MI p baseX t (fun i => (baseU i,baseR i,baseQ i)) +
      MI p baseU b (fun i => (baseA i,baseR i,baseQ i)) =
      CE p t (fun i => (baseA i,baseR i,baseQ i)) := by
    rw [MI_eq, MI_eq,CE_determined p t (fun i => ((baseU i,baseR i,baseQ i),baseX i)),sub_zero]
    · rw [CE_recover_adder p b baseR _ adder hinj (fun _ _ h => congrArg (fun s => s.2.1) h),
        CE_recover_adder p b baseR _ adder hinj (fun _ _ h => congrArg (fun s => s.2.1) h),
        source_markov pq pa pu px pr hx]
      ring
    · intro i j h
      change adder (baseX i).1 (baseR i) = adder (baseX j).1 (baseR j)
      rw [show baseX i = baseX j from congrArg (fun s : (U × R × Q) × (B × G) => s.2) h,
        show baseR i = baseR j from congrArg (fun s => s.1.2.1) h]
  rw [dst,src,MI_eq p baseR t (fun i => (baseA i,baseQ i))]
  have reorder := CE_context p t (fun i => ((baseA i,baseQ i),baseR i))
    (fun i => (baseA i,baseR i,baseQ i)) (fun i j => by simp only [Prod.mk.injEq]; tauto)
  rw [reorder,add_sub_cancel _ _]
  rfl

end RelayMaskedLaw

namespace RelayAdderUpper
open RelayEntropy RelayMaskedLaw OMA.S_itp_relay_channel RelayAdderCertificate
open scoped Classical BigOperators
variable {Q A U B G R T : Type} [Fintype Q] [Fintype A] [Fintype U] [Fintype B]
  [Fintype G] [Fintype R] [Fintype T]

noncomputable def bitLaw (pu : A × Q → U → ℝ) (px : U × Q → B × G → ℝ)
    (aq : A × Q) (b : B) := ∑ u, pu aq u * ∑ m, px (u,aq.2) (b,m)

omit [Fintype Q] [Fintype A] in
lemma bitLaw_pmf (pu : A × Q → U → ℝ) (px : U × Q → B × G → ℝ)
    (hu : IsKernel pu) (hx : IsKernel px) (aq : A × Q) : IsPmf (bitLaw pu px aq) := by
  constructor
  · intro b
    exact Finset.sum_nonneg fun u _ => mul_nonneg (hu.1 _ _) (Finset.sum_nonneg fun m _ => hx.1 _ _)
  · unfold bitLaw
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← Fintype.sum_prod_type, hx.2, mul_one]
    exact hu.2 _

noncomputable def addLaw (adder : B → R → T) (pb : B → ℝ) (pr : R → ℝ) :=
  push (fun br : B × R => adder br.1 br.2) (fun br => pb br.1 * pr br.2)

lemma addLaw_total (adder : B → R → T) (pb : B → ℝ) (pr : R → ℝ)
    (hb : ∑ b, pb b = 1) (hr : ∑ r, pr r = 1) :
    ∑ t, addLaw adder pb pr t = 1 := by
  simp [addLaw,push_total,Fintype.sum_prod_type,← Finset.mul_sum,hr,hb]

lemma condAdder (adder : B → R → T) (pq : Q → ℝ) (pa : Q → A → ℝ)
    (pu : A × Q → U → ℝ) (px : U × Q → B × G → ℝ) (pr : A × Q → R → ℝ)
    (hu : IsKernel pu) (hx : IsKernel px) (hr : IsKernel pr) :
    CE (baseLaw pq pa pu px pr) (fun i => adder (baseX i).1 (baseR i)) (fun i => (baseA i,baseQ i)) =
      ∑ q, ∑ a, pq q * pa q a * ent (addLaw adder (bitLaw pu px (a,q)) (pr (a,q))) := by
  let p := baseLaw pq pa pu px pr
  let ctx (i : State Q A U B G R) := (baseA i,baseQ i)
  let t (i : State Q A U B G R) := adder (baseX i).1 (baseR i)
  let k (aq : A × Q) := addLaw adder (bitLaw pu px aq) (pr aq)
  have hctx (q : Q) (a : A) : push ctx p (a,q) = pq q * pa q a := by
    unfold ctx p baseA baseQ baseLaw prefixLaw extend push
    simp only [Fintype.sum_prod_type, Prod.mk.injEq]
    simp [← Finset.mul_sum,hx.2,hr.2,hu.2,eq_comm, and_comm,
      ite_and, ← Fintype.sum_prod_type]
  have hj (aq : A × Q) (o : T) : push (fun i => (ctx i,t i)) p (aq,o) = push ctx p aq * k aq o := by
    obtain ⟨a,q⟩ := aq
    rw [hctx]
    unfold p ctx t baseA baseQ baseX baseR baseLaw prefixLaw extend push k addLaw bitLaw
    simp only [Fintype.sum_prod_type, Prod.mk.injEq, ite_and, ← Finset.ite_sum_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [push,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul,mul_ite,mul_zero]
    -- Align the source-mixture, relay, and mask summations.
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    by_cases he : adder b r = o
    · simp only [he,ite_true]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro m _
      ring
    · simp [he]
  change H p (fun i => (ctx i,t i)) - H p ctx = _
  rw [H_extend p ctx t k (fun aq => addLaw_total _ _ _ (bitLaw_pmf pu px hu hx aq).2 (hr.2 aq)) hj,
    add_sub_cancel_left,Fintype.sum_prod_type,Finset.sum_comm]
  simp only [hctx,k]

lemma bit_adder_inj (r : Bit) : Function.Injective fun b => integerSum b r := by
  intro a b h
  apply Fin.ext
  have he := congrArg Fin.val h
  change a.val+r.val=b.val+r.val at he
  omega

lemma bit_adder_bound (p q : Bit → ℝ) (hp : IsPmf p) (hq : IsPmf q) :
    ent (addLaw integerSum p q) ≤ 3/2 := by
  have hp2 := hp.2
  have hq2 := hq.2
  rw [Fin.sum_univ_two] at hp2 hq2
  have hp0 : p 0 = 1 - p 1 := by linarith
  have hq0 : q 0 = 1 - q 1 := by linarith
  have he : addLaw integerSum p q = ![(1-p 1)*(1-q 1),p 1*(1-q 1)+(1-p 1)*q 1,p 1*q 1] := by
    funext o
    fin_cases o <;> norm_num [addLaw,push,Fintype.sum_prod_type,Fin.sum_univ_two,integerSum,hp0,hq0]
    ring
  rw [he]
  exact independent_adder_entropy_bits _ _ (hp.1 _) (by linarith [hp.1 0]) (hq.1 _) (by linarith [hq.1 0])

lemma weighted_le (pq : Q → ℝ) (pa : Q → A → ℝ) (g : Q → A → ℝ) (c : ℝ)
    (hq : IsPmf pq) (ha : IsKernel pa) (hg : ∀ q a, g q a ≤ c) :
    ∑ q, ∑ a, pq q * pa q a * g q a ≤ c := by
  calc
    _ ≤ ∑ q, ∑ a, pq q * pa q a * c := Finset.sum_le_sum (fun q _ => Finset.sum_le_sum
      (fun a _ => mul_le_mul_of_nonneg_left (hg q a) (mul_nonneg (hq.1 _) (ha.1 _ _))))
    _ = c := by simp [← Finset.sum_mul,← Finset.mul_sum,ha.2,hq.2]

theorem one_use_upper : coverElGamalTheorem7Rate (maskedK (G := Bit) integerSum) ≤ 3/2 := by
  unfold coverElGamalTheorem7Rate
  apply Real.sSup_le
  · rintro r ⟨_,_,_,_,pq,pa,pu,px,pr,pv,hq,ha,hu,hx,hr,hv,rfl⟩
    rw [catalogue_minimum,masked_constraints integerSum bit_adder_inj pq pa pu px pr pv hq ha hu hx hr hv]
    apply le_trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [condAdder integerSum pq pa pu px pr hu hx hr]
    exact weighted_le _ _ _ _ hq ha (fun q a => bit_adder_bound _ _ (bitLaw_pmf _ _ hu hx _) ⟨hr.1 _,hr.2 _⟩)
  · norm_num

end RelayAdderUpper

namespace RelayFullObservation
open RelayEntropy RelayMaskedLaw RelayAdderUpper OMA.S_itp_relay_channel
open scoped Classical BigOperators
variable {Ω B G R T V C E : Type} [Fintype Ω] [Fintype B] [Fintype G] [Fintype R] [Fintype T]
  [Fintype V] [Fintype C] [Fintype E]

lemma MI_left (p : Ω → ℝ) (x : Ω → B) (y : Ω → V) (c : Ω → C) :
    MI p x y c = CE p x c - CE p x (fun i => (c i,y i)) := by
  have h : MI p x y c = MI p y x c := by
    unfold MI
    rw [cmi_push,cmi_push]
    rw [H_partition p (fun i => (x i,y i,c i)) (fun i => (y i,x i,c i))
      (fun i j => by simp only [Prod.mk.injEq]; tauto)]
    ring
  rw [h,MI_eq]

noncomputable def point (x : B) (y : B) : ℝ := if y=x then 1 else 0

omit [Fintype E] in
lemma point_kernel (f : E → B) : IsKernel (fun i => point (f i)) := by
  exact ⟨fun i b => by change 0 ≤ (if b=f i then (1:ℝ) else 0); positivity, fun i => by simp [point]⟩

omit [Fintype B] in
lemma extend_point (p : Ω → ℝ) (f : Ω → B) :
    extend p (fun i => point (f i)) = push (fun i => (i,f i)) p := by
  funext ⟨i,b⟩
  simp [extend,point,push,Prod.mk.injEq,ite_and,eq_comm,mul_ite]

lemma CE_push (p : Ω → ℝ) (f : Ω → B) (x : B → V) (c : B → C) :
    CE (push f p) x c = CE p (fun i => x (f i)) (fun i => c (f i)) := by
  simp only [CE,H_push]

abbrev Tiny := Fin 1

noncomputable def single (_ : Tiny) : ℝ := 1
lemma single_pmf : IsPmf single := by simp [IsPmf,single]
lemma single_kernel {I : Type} : IsKernel (fun _ : I => single) :=
  ⟨fun _ => single_pmf.1,fun _ => single_pmf.2⟩

noncomputable def fullConstraints [AddGroup G] (adder : B → R → T) (px : B × G → ℝ) (pr : R → ℝ)
    (e : B × G ≃ V) :=
  rowThree (thm7Joint (maskedK adder) single (fun _ => single) (fun _ => single)
    (fun _ => px) (fun _ => pr) (fun i v => point (e i.2.2.1) v))

set_option maxHeartbeats 1500000 in
theorem full_constraints [AddGroup G] (adder : B → R → T) (hinj : ∀ r, Function.Injective (fun b => adder b r))
    (px : B × G → ℝ) (pr : R → ℝ) (hx : IsPmf px) (hr : IsPmf pr) (e : B × G ≃ V) :
    fullConstraints adder px pr e = (ent (addLaw adder (push Prod.fst px) pr),ent px,
      ent (addLaw adder (push Prod.fst px) pr)) := by
  let p := baseLaw single (fun _ => single) (fun _ => single) (fun _ => px) (fun _ => pr)
  let t (i : State Tiny Tiny Tiny B G R) := adder (baseX i).1 (baseR i)
  let q := @baseQ Tiny Tiny Tiny B R G
  let a := @baseA Tiny Tiny Tiny B R G
  let r := @baseR Tiny Tiny Tiny B R G
  let x := @baseX Tiny Tiny Tiny B R G
  let u := @baseU Tiny Tiny Tiny B R G
  let y (s : (State Tiny Tiny Tiny B G R × G) × V) := (t s.1.1,(baseX s.1.1).2+s.1.2)
  let z (s : (State Tiny Tiny Tiny B G R × G) × V) := ((baseX s.1.1).1,s.1.2)
  let f (j : State Tiny Tiny Tiny B G R × G) := e ((baseX j.1).1,j.2)
  let k (j : State Tiny Tiny Tiny B G R × G) := point (f j)
  let pN := extend p (fun _ => uniform G)
  let μ := extend pN k
  let c (s : (State Tiny Tiny Tiny B G R × G) × V) := (r s.1.1,y s)
  have hxk : IsKernel (fun _ : Tiny × Tiny => px) := ⟨fun _ => hx.1,fun _ => hx.2⟩
  have hrk : IsKernel (fun _ : Tiny × Tiny => pr) := ⟨fun _ => hr.1,fun _ => hr.2⟩
  have hv := point_kernel (fun i : Tiny × R × (B × G) × Tiny => e i.2.2.1)
  have hk : IsKernel k := point_kernel f
  have hp : ∑ i, p i = 1 := base_total _ _ _ _ _ single_pmf single_kernel single_kernel hxk hrk
  have re : ∀ i j, c i = c j → (x i.1.1 = x j.1.1 ↔ z i = z j) := by
    intro i j h
    exact masked_recovery (congrArg (fun t => t.2.2) h)
  have hmargin : MI μ z Prod.snd (fun s => (u s.1.1,r s.1.1,y s,q s.1.1)) =
      CE μ (fun s => x s.1.1) c := by
    rw [MI_left]
    have hz : CE μ z (fun i => ((u i.1.1,r i.1.1,y i,q i.1.1),i.2)) = 0 := by
      change CE (extend pN (fun i => point (f i))) z _ = 0
      rw [extend_point,CE_push]
      apply CE_determined
      intro i j h
      apply e.injective
      exact congrArg (fun w : (Tiny × R × (T × G) × Tiny) × V => w.2) h
    rw [hz,sub_zero, CE_context μ z _ c (fun i j => by simp [c,Prod.mk.injEq,Subsingleton.elim (u i.1.1) (u j.1.1),Subsingleton.elim (q i.1.1) (q j.1.1)])]
    unfold CE
    congr 1
    apply H_partition
    intro i j
    simp only [Prod.mk.injEq]
    exact ⟨fun h => ⟨h.1,(re i j h.1).2 h.2⟩,fun h => ⟨h.1,(re i j h.1).1 h.2⟩⟩
  have mi : MI μ (fun s => x s.1.1) y (fun s => r s.1.1) = CE p t r := by
    have h := masked_MI p hp k hk x t r (fun i => Equiv.addLeft (x i).2)
    refine h.trans ?_
    rw [MI_eq, CE_determined p t (fun i => (r i,x i)),sub_zero]
    intro i j h
    change adder (x i).1 (r i) = adder (x j).1 (r j)
    rw [show x i = x j from congrArg (fun w : R × (B × G) => w.2) h,
      show r i = r j from congrArg (fun w : R × (B × G) => w.1) h]
  rw [MI_left] at mi
  have hxR : CE μ (fun s => x s.1.1) (fun s => r s.1.1) = ent px := by
    rw [CE_drop _ k hk.2 (fun j => x j.1) (fun j => r j.1),
      CE_drop _ _ (fun _ => uniform_total) x r]
    let pref := prefixLaw single (fun _ => single) (fun _ => single) (fun _ => pr)
    change CE (extend pref (fun _ => px)) (fun s => s.2) (fun s => s.1.2) = ent px
    refine (CE_next pref (fun _ => px) (fun _ => hx.2) Prod.snd (fun _ => id) (fun _ => px)
      (fun _ => hx.2) (fun _ => push_id px)).trans ?_
    rw [← Finset.sum_mul]
    have hs : ∑ i, prefixLaw single (fun _ => single) (fun _ => single) (fun _ => pr) i = 1 := by
      simp [prefixLaw,Fintype.sum_prod_type,single,hr.2]
    change (∑ i, pref i) * ent px = ent px
    rw [show (∑ i, pref i) = 1 from hs,one_mul]
  have hm : CE p t (fun i => (a i,r i,q i)) +
      MI μ z Prod.snd (fun s => (u s.1.1,r s.1.1,y s,q s.1.1)) = ent px := by
    rw [CE_context p t _ r (fun i j => by simp [Subsingleton.elim (a i) (a j),Subsingleton.elim (q i) (q j)]),hmargin]
    change CE μ (fun s => x s.1.1) (fun s => r s.1.1) - CE μ (fun s => x s.1.1) c = CE p t r at mi
    linarith
  have hd : CE p t (fun i => (a i,q i)) = ent (addLaw adder (push Prod.fst px) pr) := by
    rw [condAdder adder single (fun _ => single) (fun _ => single) (fun _ => px)
      (fun _ => pr) single_kernel hxk hrk]
    simp only [Fin.sum_univ_one,single,one_mul,mul_one]
    congr 2
    funext b
    simp [bitLaw,single,push,Fintype.sum_prod_type]
    rw [Finset.sum_comm (f := fun (x : B) (m : G) => if x=b then px (x,m) else 0)]
    simp
  have hq : CE p t q = CE p t (fun i => (a i,q i)) :=
    CE_context _ _ _ _ (fun _ _ => iff_of_true (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  unfold fullConstraints
  rw [masked_constraints adder hinj _ _ _ _ _ _ single_pmf single_kernel single_kernel hxk hrk hv]
  change (CE p t q, CE p t (fun i => (a i,r i,q i)) + MI μ z Prod.snd
    (fun s => (u s.1.1,r s.1.1,y s,q s.1.1)), CE p t (fun i => (a i,q i))) = _
  rw [hm,hq,hd]


end RelayFullObservation

namespace RelayCodeSimulation
open OMA.S_itp_relay_channel
open scoped BigOperators Classical

structure Code (X R Y Z : Type) (n M : ℕ) where
  enc : Fin M → Fin n → X
  relay : (i : Fin n) → (Fin i.val → Z) → R
  dec : (Fin n → Y) → Fin M

variable {X R Y Z : Type} {n M : ℕ}

def past (z : Fin n → Z) (i : Fin n) (j : Fin i.val) := z ⟨j.val, j.isLt.trans i.isLt⟩

noncomputable def path (K : X × R → Y × Z → ℝ) (c : Code X R Y Z n M)
    (m : Fin M) (z : Fin n → Z) (y : Fin n → Y) :=
  ∏ i, K (c.enc m i,c.relay i (past z i)) (y i,z i)

noncomputable def loss [Fintype Y] [Fintype Z] (K : X × R → Y × Z → ℝ) (c : Code X R Y Z n M)
    (m : Fin M) := ∑ z, ∑ y, if c.dec y ≠ m then path K c m z y else 0

noncomputable def err [Fintype Y] [Fintype Z] (K : X × R → Y × Z → ℝ) (c : Code X R Y Z n M) :=
  (1 / (M:ℝ)) * ∑ m, loss K c m

def idx (i : Fin n) (b : Fin 2) : Fin (n*2) := finProdFinEquiv (i,b)

def words {S T : Type} (e : T ≃ S × S) (n : ℕ) : (Fin (n*2) → S) ≃ (Fin n → T) where
  toFun w i := e.symm (w (idx i 0),w (idx i 1))
  invFun w k := let ib := finProdFinEquiv.symm k
                if ib.2 = 0 then (e (w ib.1)).1 else (e (w ib.1)).2
  left_inv w := by
    funext k
    obtain ⟨⟨i,b⟩,rfl⟩ := finProdFinEquiv.surjective k
    fin_cases b <;> simp [idx]
  right_inv w := by
    funext i
    simp [idx]

structure PairSim {X' R' Y' Z' : Type} (K : X × R → Y × Z → ℝ) (L : X' × R' → Y' × Z' → ℝ) where
  src : X' ≃ X × X
  dest : Y' ≃ Y × Y
  obs : Z' ≃ Z × Z
  first : R' → R
  next : R' → Z → R
  factor : ∀ x s y z, L (x,s) (y,z) =
    K ((src x).1,first s) ((dest y).1,(obs z).1) *
    K ((src x).2,next s (obs z).1) ((dest y).2,(obs z).2)

namespace PairSim
variable {X' R' Y' Z' : Type} {K : X × R → Y × Z → ℝ} {L : X' × R' → Y' × Z' → ℝ}

def act (d : PairSim K L) (c : Code X' R' Y' Z' n M)
    (i : Fin n) (b : Fin 2) (h : Fin (idx i b).val → Z) : R := by
  let old : Fin i.val → Z' := fun j => d.obs.symm
    (h ⟨2*j.val, by change _ < b.val + 2*i.val; omega⟩,
     h ⟨2*j.val+1, by change _ < b.val + 2*i.val; omega⟩)
  let s := c.relay i old
  exact if hb : b=0 then d.first s else d.next s
    (h ⟨2*i.val,by change _ < b.val + 2*i.val; have := b.isLt; have : b.val ≠ 0 := fun he => hb (Fin.ext he); omega⟩)

def run (d : PairSim K L) (c : Code X' R' Y' Z' n M) : Code X R Y Z (n*2) M where
  enc m := (words d.src n).symm (c.enc m)
  relay := Equiv.piCongrLeft (fun k : Fin (n*2) => (Fin k.val → Z) → R) finProdFinEquiv
    (fun t => d.act c t.1 t.2)
  dec w := c.dec (words d.dest n w)

lemma run_enc (d : PairSim K L) (c : Code X' R' Y' Z' n M) (m : Fin M) (i : Fin n) :
    ((d.run c).enc m (idx i 0),(d.run c).enc m (idx i 1)) = d.src (c.enc m i) := by
  change ( (if (finProdFinEquiv.symm (idx i 0)).2 = 0 then _ else _),
    (if (finProdFinEquiv.symm (idx i 1)).2 = 0 then _ else _)) = _
  simp only [idx,Equiv.symm_apply_apply, if_true, (by decide : (1 : Fin 2) ≠ 0), if_false]

lemma run_relay (d : PairSim K L) (c : Code X' R' Y' Z' n M) (z : Fin (n*2) → Z) (i : Fin n) :
    let s := c.relay i (past (words d.obs n z) i)
    ((d.run c).relay (idx i 0) (past z (idx i 0)), (d.run c).relay (idx i 1) (past z (idx i 1))) =
      (d.first s, d.next s (z (idx i 0))) := by
  have hact (b : Fin 2) : (d.run c).relay (idx i b) = d.act c i b := by
    exact Equiv.piCongrLeft_apply_apply _ _ _ (i,b)
  rw [hact,hact]
  simp only [act, dite_true, dif_neg (by decide : (1 : Fin 2) ≠ 0)]
  congr 1 <;> congr 1 <;> try congr 1
  all_goals first
    | rfl
    | (apply congrArg z; apply Fin.ext; simp [idx])
    | (funext j; apply congrArg; apply Prod.ext <;> apply congrArg z <;> apply Fin.ext <;> simp [idx, Nat.add_comm])

lemma path_pair (d : PairSim K L) (c : Code X' R' Y' Z' n M)
    (m : Fin M) (z : Fin (n*2) → Z) (y : Fin (n*2) → Y) :
    path K (d.run c) m z y = path L c m (words d.obs n z) (words d.dest n y) := by
  unfold path
  rw [← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.prod_univ_two,d.factor]
  have he := d.run_enc c m i
  have hr := d.run_relay c z i
  dsimp only at hr
  change K (_,_) (_,_) * K (_,_) (_,_) = _
  simp only [words,Equiv.coe_fn_mk, Equiv.apply_symm_apply]
  have h0 : (d.run c).relay (idx i 0) (past z (idx i 0)) = _ := congrArg Prod.fst hr
  have h1 : (d.run c).relay (idx i 1) (past z (idx i 1)) = _ := congrArg Prod.snd hr
  dsimp only at h0 h1
  rw [← he]
  change K (_, (d.run c).relay (idx i 0) _) _ * K (_, (d.run c).relay (idx i 1) _) _ = _
  unfold idx at h0 h1 ⊢
  rw [h0,h1]
  rfl

lemma err_pair [Fintype Y] [Fintype Z] [Fintype Y'] [Fintype Z']
    (d : PairSim K L) (c : Code X' R' Y' Z' n M) : err K (d.run c) = err L c := by
  unfold err loss
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  apply Fintype.sum_equiv (words d.obs n)
  intro z
  apply Fintype.sum_equiv (words d.dest n)
  intro y
  rw [d.path_pair c m z y]
  rfl

end PairSim
end RelayCodeSimulation

namespace RelayCodeSimulation
open OMA.S_itp_relay_channel
open scoped BigOperators Classical
variable {X R Y Z : Type} [Fintype Y] [Fintype Z] {n M : ℕ}
variable {K : X × R → Y × Z → ℝ}

def Code.pad (c : Code X R Y Z n M) (x : X) (r : R) : Code X R Y Z (n+1) M where
  enc m := Fin.snoc (c.enc m) x
  relay := Fin.lastCases (motive := fun k : Fin (n+1) => (Fin k.val → Z) → R)
    (fun _ => r) (fun i => c.relay i)
  dec y := c.dec (Fin.init y)

omit [Fintype Y] [Fintype Z] in
lemma path_pad (c : Code X R Y Z n M) (x : X) (r : R) (m : Fin M)
    (z : Fin n → Z) (y : Fin n → Y) (z' : Z) (y' : Y) :
    path K (c.pad x r) m (Fin.snoc z z') (Fin.snoc y y') = path K c m z y * K (x,r) (y',z') := by
  simp only [path, Fin.prod_univ_castSucc, Code.pad, Fin.snoc_castSucc,Fin.snoc_last,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have he : past (Fin.snoc z z') i.castSucc = past z i := by
    funext j
    exact @Fin.snoc_castSucc n (fun _ => Z) z' z ⟨j.val,j.isLt.trans i.isLt⟩
  rw [he]

lemma err_pad (hK : IsKernel K) (c : Code X R Y Z n M) (x : X) (r : R) :
    err K (c.pad x r) = err K c := by
  unfold err loss
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Z)).sum_comp,Fintype.sum_prod_type]
  simp_rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Y)).sum_comp,
    Fintype.sum_prod_type]
  change (∑ z', ∑ z, ∑ y', ∑ y, if (c.pad x r).dec (Fin.snoc y y') ≠ m then
    path K (c.pad x r) m (Fin.snoc z z') (Fin.snoc y y') else 0) = _
  simp_rw [path_pad]
  simp only [Code.pad,Fin.init_snoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  conv_lhs => enter [2,z',2,y']; rw [Finset.sum_congr rfl (fun y _ =>
    show (if c.dec y ≠ m then path K c m z y * K (x,r) (y',z') else 0) =
      (if c.dec y ≠ m then path K c m z y else 0) * K (x,r) (y',z') by split_ifs <;> simp)]
  simp_rw [← Finset.sum_mul,← Finset.mul_sum]
  rw [Finset.sum_comm,← Fintype.sum_prod_type,hK.2,mul_one]

lemma can_trim {M' : ℕ} (hM' : 0 < M') (hM : M' ≤ M) (hK : IsKernel K)
    (c : Code X R Y Z n M) : ∃ d : Code X R Y Z n M', err K d ≤ err K c := by
  have hpos := hM'.trans_le hM
  let : NeZero M := ⟨hpos.ne'⟩
  let : NeZero M' := ⟨hM'.ne'⟩
  let f (a : Fin M) (i : Fin M') := a + Fin.castLE hM i
  let sumloss a := ∑ i, loss K c (f a i)
  have ht : ∑ a, sumloss a = (M':ℝ) * ∑ m, loss K c m := by
    unfold sumloss
    rw [Finset.sum_comm]
    have he (i : Fin M') : (∑ a, loss K c (f a i)) = ∑ m, loss K c m :=
      Equiv.sum_comp (Equiv.addRight (Fin.castLE hM i)) (loss K c)
    simp [he]
  have hav : ∃ a, (M:ℝ) * sumloss a ≤ (M':ℝ) * ∑ m, loss K c m := by
    by_contra! h
    have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin M)) (fun a _ => h a)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum,ht] at hs
    exact lt_irrefl _ hs
  obtain ⟨a,ha⟩ := hav
  have hi : Function.Injective (f a) := fun i j h => Fin.ext (congrArg (fun t : Fin M => t.val) (show Fin.castLE hM i = Fin.castLE hM j from add_left_cancel h))
  let d : Code X R Y Z n M' := ⟨fun i => c.enc (f a i),c.relay,fun y => Function.invFun (f a) (c.dec y)⟩
  refine ⟨d,?_⟩
  have hl (i : Fin M') : loss K d i ≤ loss K c (f a i) := by
    apply Finset.sum_le_sum
    intro z _
    apply Finset.sum_le_sum
    intro y _
    have hn : 0 ≤ path K c (f a i) z y := Finset.prod_nonneg (fun _ _ => hK.1 _ _)
    by_cases he : c.dec y = f a i
    · simp [d,he,Function.leftInverse_invFun hi i]
    · simp only [he,ne_eq,not_false_eq_true,ite_true]
      split_ifs
      · exact hn
      · exact le_rfl
  have hi' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  unfold err
  rw [one_div,one_div,← div_eq_inv_mul,← div_eq_inv_mul]
  apply (div_le_div_iff₀ (by exact_mod_cast hM') (by exact_mod_cast hpos)).2
  change (∑ i, loss K d i) * M ≤ _ 
  have h' := mul_le_mul_of_nonneg_left hi' (by positivity : (0:ℝ) ≤ M)
  change (M:ℝ) * _ ≤ (M:ℝ) * sumloss a at h'
  linarith

noncomputable def messages (n : ℕ) (v : ℝ) := max 1 ⌊(2:ℝ) ^ ((n:ℝ)*v)⌋₊

lemma achievable_iff [Fintype X] [Fintype R] (v : ℝ) : IsRelayAchievable K v ↔
    0 ≤ v ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ c : Code X R Y Z n (messages n v), err K c ≤ ε := by
  constructor
  · rintro ⟨hv,hh⟩
    refine ⟨hv,fun ε he => ?_⟩
    obtain ⟨N,hN⟩ := hh ε he
    refine ⟨N,fun n hn => ?_⟩
    obtain ⟨e,r,d,h⟩ := hN n hn
    exact ⟨⟨e,r,d⟩,h⟩
  · rintro ⟨hv,hh⟩
    refine ⟨hv,fun ε he => ?_⟩
    obtain ⟨N,hN⟩ := hh ε he
    refine ⟨N,fun n hn => ?_⟩
    obtain ⟨c,h⟩ := hN n hn
    exact ⟨c.enc,c.relay,c.dec,h⟩

variable {X' R' Y' Z' : Type} [Fintype X] [Fintype R] [Fintype X'] [Fintype R']
  [Fintype Y'] [Fintype Z'] {L : X' × R' → Y' × Z' → ℝ}

/-- Every strictly smaller per-use rate runs at every sufficiently large physical length. -/
theorem PairSim.achievable (d : PairSim K L) (hK : IsKernel K) (x₀ : X) (r₀ : R)
    {s v : ℝ} (hs : IsRelayAchievable L s) (hv : 0 ≤ v) (hvs : 2*v < s) :
    IsRelayAchievable K v := by
  rw [achievable_iff] at hs ⊢
  refine ⟨hv,fun ε he => ?_⟩
  obtain ⟨N,hN⟩ := hs.2 ε he
  obtain ⟨D,hD⟩ := exists_nat_gt (v/(s-2*v))
  have hgap := (div_lt_iff₀ (by linarith : 0 < s-2*v)).1 hD
  refine ⟨2*(max N D),fun n hn => ?_⟩
  let k := n/2
  have hkN : N ≤ k := by dsimp [k]; omega
  have hkD : D ≤ k := by dsimp [k]; omega
  have hlen : n=k*2 ∨ n=k*2+1 := by dsimp [k]; omega
  have he' : (n:ℝ)*v ≤ (k:ℝ)*s := by
    have hkDr : (D:ℝ) ≤ k := by exact_mod_cast hkD
    have h := mul_le_mul_of_nonneg_right hkDr (by linarith : 0 ≤ s-2*v)
    rcases hlen with hlen | hlen <;> rw [hlen] <;> push_cast <;> nlinarith
  have hcount : messages n v ≤ messages k s := max_le_max_left _ (Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) he'))
  obtain ⟨c,hc⟩ := hN k hkN
  obtain ⟨c',hc'⟩ := can_trim (M' := messages n v) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    hcount hK (d.run c)
  have hε := hc'.trans ((d.err_pair c).le.trans hc)
  have transport {j : ℕ} (h : j=n) (c : Code X R Y Z j (messages n v)) (hc : err K c ≤ ε) :
      ∃ c : Code X R Y Z n (messages n v), err K c ≤ ε := by
    subst j
    exact ⟨c,hc⟩
  rcases hlen with hlen | hlen
  · exact transport hlen.symm c' hε
  · exact transport hlen.symm (c'.pad x₀ r₀) ((err_pad hK c' _ _).le.trans hε)

end RelayCodeSimulation

namespace RelayRelabel
open RelayEntropy RelayCodeSimulation OMA.S_itp_relay_channel
open scoped BigOperators Classical
variable {X R Y Z X' R' Y' Z' : Type}
variable [Fintype X] [Fintype R] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype R'] [Fintype Y'] [Fintype Z']
variable {K : X × R → Y × Z → ℝ} {L : X' × R' → Y' × Z' → ℝ}

structure Iso (K : X × R → Y × Z → ℝ) (L : X' × R' → Y' × Z' → ℝ) where
  x : X ≃ X'
  r : R ≃ R'
  y : Y ≃ Y'
  z : Z ≃ Z'
  law : ∀ x₀ r₀ y₀ z₀, L (x x₀,r r₀) (y y₀,z z₀) = K (x₀,r₀) (y₀,z₀)

def Iso.symm (d : Iso K L) : Iso L K where
  x := d.x.symm
  r := d.r.symm
  y := d.y.symm
  z := d.z.symm
  law x r y z := by simpa using (d.law (d.x.symm x) (d.r.symm r) (d.y.symm y) (d.z.symm z)).symm

omit [Fintype X] [Fintype R] [Fintype X'] [Fintype R'] in
lemma Iso.kernel (d : Iso K L) (hk : IsKernel K) : IsKernel L := by
  constructor
  · rintro ⟨x,r⟩ ⟨y,z⟩
    rw [d.symm.law x r y z |>.symm]
    exact hk.1 _ _
  · rintro ⟨x,r⟩
    rw [← (d.y.prodCongr d.z).sum_comp]
    refine Eq.trans (Finset.sum_congr rfl (fun o _ => ?_)) (hk.2 (d.x.symm x,d.r.symm r))
    obtain ⟨y,z⟩ := o
    simpa using d.law (d.x.symm x) (d.r.symm r) y z

def Iso.code (d : Iso K L) {n M} (c : Code X R Y Z n M) : Code X' R' Y' Z' n M where
  enc m i := d.x (c.enc m i)
  relay i h := d.r (c.relay i fun j => d.z.symm (h j))
  dec y := c.dec fun i => d.y.symm (y i)

omit [Fintype X] [Fintype R] [Fintype X'] [Fintype R'] in
lemma Iso.err (d : Iso K L) {n M} (c : Code X R Y Z n M) : err L (d.code c) = err K c := by
  unfold RelayCodeSimulation.err loss
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  symm
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) d.z)
  intro z
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) d.y)
  intro y
  simp [code,path,past,d.law]
  rfl

lemma Iso.ach (d : Iso K L) {v} (h : IsRelayAchievable K v) : IsRelayAchievable L v := by
  refine ⟨h.1,fun ε he => ?_⟩
  obtain ⟨N,hN⟩ := h.2 ε he
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨ee,rr,dd,hh⟩ := hN n hn
  let c : Code X R Y Z n _ := ⟨ee,rr,dd⟩
  exact ⟨(d.code c).enc,(d.code c).relay,(d.code c).dec,(d.err c).le.trans hh⟩

lemma Iso.cap (d : Iso K L) : relayCapacity K = relayCapacity L := by
  unfold relayCapacity
  congr 1
  ext v
  exact ⟨d.ach,d.symm.ach⟩

variable {Q A U V : Type} [Fintype Q] [Fintype A] [Fintype U] [Fintype V]

lemma MI_equiv {Ω X₁ X₂ Y₁ Y₂ C₁ C₂ : Type} [Fintype Ω] [Fintype X₁] [Fintype X₂] [Fintype Y₁]
    [Fintype Y₂] [Fintype C₁] [Fintype C₂] (p : Ω → ℝ) (x₁ : Ω → X₁) (x₂ : Ω → X₂)
    (y₁ : Ω → Y₁) (y₂ : Ω → Y₂) (c₁ : Ω → C₁) (c₂ : Ω → C₂)
    (hx : ∀ i j, x₁ i = x₁ j ↔ x₂ i = x₂ j)
    (hy : ∀ i j, y₁ i = y₁ j ↔ y₂ i = y₂ j)
    (hc : ∀ i j, c₁ i = c₁ j ↔ c₂ i = c₂ j) :
    MI p x₁ y₁ c₁ = MI p x₂ y₂ c₂ := by
  unfold MI
  rw [cmi_push,cmi_push]
  congr 1
  · congr 1
    · congr 1 <;> apply H_partition <;> intro i j <;> simp only [Prod.mk.injEq,hx,hy,hc]
    · apply H_partition; intro i j; simp only [Prod.mk.injEq,hx,hy,hc]
  · exact H_partition p _ _ hc

abbrev Row (Q A U X R Y Z V : Type) := Q × A × U × X × R × Y × Z × V

def Iso.row (d : Iso K L) : Row Q A U X R Y Z V ≃ Row Q A U X' R' Y' Z' V :=
  (Equiv.refl Q).prodCongr ((Equiv.refl A).prodCongr ((Equiv.refl U).prodCongr
    (d.x.prodCongr (d.r.prodCongr (d.y.prodCongr (d.z.prodCongr (Equiv.refl V)))))))

omit [Fintype X'] [Fintype R'] [Fintype Y'] [Fintype Z'] in
lemma Iso.joint (d : Iso K L) (pq : Q → ℝ) (pa : Q → A → ℝ) (pu : A × Q → U → ℝ)
    (px : U × Q → X → ℝ) (pr : A × Q → R → ℝ) (pv : U × R × Z × Q → V → ℝ) :
    thm7Joint L pq pa pu (fun i x => px i (d.x.symm x)) (fun i r => pr i (d.r.symm r))
      (fun i => pv (i.1,d.r.symm i.2.1,d.z.symm i.2.2.1,i.2.2.2)) =
      push d.row (thm7Joint K pq pa pu px pr pv) := by
  funext t
  obtain ⟨⟨q,a,u,x,r,y,z,v⟩,rfl⟩ := d.row.surjective t
  simp only [push,Equiv.apply_eq_iff_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [row,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,thm7Joint,Equiv.symm_apply_apply,d.law]

set_option maxHeartbeats 800000 in
lemma Iso.minRate (d : Iso K L) (p : Row Q A U X R Y Z V → ℝ) :
    thm7MinRate (push d.row p) = thm7MinRate p := by
  rw [catalogue_minimum,catalogue_minimum]
  apply congrArg minimum
  change rowThree (push (fun t : Row Q A U X R Y Z V => (t.1,t.2.1,t.2.2.1,d.x t.2.2.2.1,
    d.r t.2.2.2.2.1,d.y t.2.2.2.2.2.1,d.z t.2.2.2.2.2.2.1,t.2.2.2.2.2.2.2)) p) = _
  rw [three_push]
  unfold rowThree three
  repeat' first
    | (apply MI_equiv <;> intro i j <;> solve | simp only [Prod.mk.injEq,Equiv.apply_eq_iff_eq])
    | apply congrArg₂ Prod.mk
    | apply congrArg₂ HSub.hSub
    | apply congrArg₂ HAdd.hAdd

/-- Rates before taking the supremum in the catalogue definition. -/
def candidateRates (W : X × R → Y × Z → ℝ) : Set ℝ :=
  {s | ∃ q a u v pq pa pu px pr pv, IsPmf pq ∧ IsKernel pa ∧ IsKernel pu ∧
    IsKernel px ∧ IsKernel pr ∧ IsKernel pv ∧
    s = thm7MinRate (@thm7Joint X R Y Z (Fin q) (Fin a) (Fin u) (Fin v) W pq pa pu px pr pv)}

lemma Iso.candidates (e : Iso K L) : candidateRates K ⊆ candidateRates L := by
  rintro s ⟨q,a,u,v',pq,pa,pu,px,pr,pv,hq,ha,hu,hx,hr,hv,he⟩
  refine ⟨q,a,u,v',pq,pa,pu,fun i x => px i (e.x.symm x),fun i r => pr i (e.r.symm r),
    fun i => pv (i.1,e.r.symm i.2.1,e.z.symm i.2.2.1,i.2.2.2),hq,ha,hu,
    ⟨fun _ _ => hx.1 _ _,fun i => (Equiv.sum_comp e.x.symm (px i)).trans (hx.2 _)⟩,
    ⟨fun _ _ => hr.1 _ _,fun i => (Equiv.sum_comp e.r.symm (pr i)).trans (hr.2 _)⟩,
    ⟨fun _ _ => hv.1 _ _,fun _ => hv.2 _⟩,?_⟩
  rw [e.joint,e.minRate,he]

lemma Iso.rate (d : Iso K L) : coverElGamalTheorem7Rate K = coverElGamalTheorem7Rate L :=
  congrArg sSup (Set.Subset.antisymm d.candidates d.symm.candidates)

/-- Transfer the universally quantified catalogue hypothesis to arbitrary named finite alphabets. -/
lemma of_universal (hyp : type_of% @OMA.S_itp_relay_channel.main) (hK : IsKernel K) :
    relayCapacity K = coverElGamalTheorem7Rate K := by
  let ex := Fintype.equivFin X
  let er := Fintype.equivFin R
  let ey := Fintype.equivFin Y
  let ez := Fintype.equivFin Z
  let L (i : Fin (Fintype.card X) × Fin (Fintype.card R)) (o : Fin (Fintype.card Y) × Fin (Fintype.card Z)) :=
    K (ex.symm i.1,er.symm i.2) (ey.symm o.1,ez.symm o.2)
  let d : Iso K L := ⟨ex,er,ey,ez,fun x r y z => by simp [L]⟩
  exact d.cap.trans ((hyp _ _ _ _ L (d.kernel hK)).trans d.rate.symm)

end RelayRelabel

namespace RelayConcrete
open RelayEntropy RelayMaskedLaw RelayAdderUpper RelayCodeSimulation RelayAdderCertificate OMA.S_itp_relay_channel
open scoped BigOperators Classical
abbrev BB := Bit × Bit
abbrev TT := Fin 3 × Fin 3

def adder₂ (b s : BB) : TT :=
  (integerSum b.1 s.1,integerSum b.2 (secondInput s.1 s.2 (b.1,0)))

theorem adder₂_inj (s : BB) : Function.Injective (fun b => adder₂ b s) := by
  intro i j h
  have h1 := bit_adder_inj s.1 (congrArg Prod.fst h)
  have h2 := congrArg Prod.snd h
  change integerSum i.2 (secondInput _ _ (i.1,0)) = integerSum j.2 (secondInput _ _ (j.1,0)) at h2
  rw [h1] at h2
  exact Prod.ext h1 (bit_adder_inj _ h2)

noncomputable abbrev K := maskedK (G := Bit) integerSum
noncomputable abbrev L := maskedK (G := BB) adder₂

lemma masked_kernel {B R T G : Type} [Fintype B] [Fintype T] [Fintype G] [AddGroup G]
    (adder : B → R → T) : IsKernel (maskedK (G := G) adder) := by
  refine ⟨fun i o => Finset.sum_nonneg fun n _ => ?_,fun i => (push_total _ _).trans uniform_total⟩
  split_ifs
  · unfold uniform; positivity
  · exact le_rfl

lemma masked_value {B R T G : Type} [Fintype G] [AddGroup G] (a : B → R → T)
    (x : B × G) (r : R) (y : T × G) (z : B × G) :
    maskedK a (x,r) (y,z) = if maskedOut a x r z.2 = (y,z) then uniform G z.2 else 0 := by
  unfold maskedK push
  calc
    _ = _ := Finset.sum_eq_single z.2 (fun n _ hn => if_neg (fun h => hn
      (congrArg (fun o : (T × G) × (B × G) => o.2.2) h))) (by simp)
    _ = _ := by by_cases h : maskedOut a x r z.2 = (y,z) <;> simp [h]

def transpose {A B : Type} : (A × A) × (B × B) ≃ (A × B) × (A × B) where
  toFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
  invFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def bMass (b : BB) : ℝ := if b.1=b.2 then 1/3 else 1/6
noncomputable def pmask {B G : Type} [Fintype G] (p : B → ℝ) (x : B × G) := p x.1 * uniform G x.2

lemma uniform_pmf {G : Type} [Fintype G] [Nonempty G] : IsPmf (uniform G) :=
  ⟨fun _ => by unfold uniform; positivity,uniform_total⟩

lemma pmask_pmf {B G : Type} [Fintype B] [Fintype G] [Nonempty G]
    (p : B → ℝ) (hp : IsPmf p) : IsPmf (pmask (G := G) p) := by
  refine ⟨fun x => mul_nonneg (hp.1 _) (uniform_pmf.1 _),?_⟩
  simp [pmask,Fintype.sum_prod_type,← Finset.mul_sum,uniform_total,hp.2]

lemma unmask {B G : Type} [Fintype B] [Fintype G] [Nonempty G] (p : B → ℝ) :
    push Prod.fst (pmask (G := G) p) = p := by
  funext b
  simp [push,pmask,Fintype.sum_prod_type,← Finset.mul_sum,uniform_total]

lemma bMass_pmf : IsPmf bMass := by
  refine ⟨fun _ => by unfold bMass; positivity,?_⟩
  norm_num [bMass,Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The pushforward of the source and strategy pmfs is the exact nine-cell histogram. -/
lemma block_output : addLaw adder₂ bMass (uniform BB) = fun o : Fin 3 × Fin 3 => (massMatrix o.1 o.2 : ℝ) / 24 := by
  funext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [addLaw,push,Fintype.sum_prod_type,Fin.sum_univ_two,
    bMass,uniform,adder₂,integerSum,secondInput,massMatrix, Matrix.vecHead,Matrix.vecTail]

lemma one_output : ent (addLaw integerSum (uniform Bit) (uniform Bit)) = 3/2 := by
  have he : addLaw integerSum (uniform Bit) (uniform Bit) = ![1/4,1/2,1/4] := by
    funext i
    fin_cases i <;> norm_num [addLaw,push,uniform,Fintype.sum_prod_type,Fin.sum_univ_two,integerSum]
  have h4 : Real.log 4 = 2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  rw [he]
  norm_num [ent,Fin.sum_univ_succ,Real.negMulLog,Matrix.vecHead,Matrix.vecTail]
  simp only [one_div,Real.log_inv,h4]
  field_simp [show Real.log 2 ≠ 0 from (Real.log_pos (by norm_num)).ne']
  ring

lemma one_input : ent (pmask (G := Bit) (uniform Bit)) = 2 := by
  have h4 : Real.log 4 = 2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  norm_num [ent,pmask,uniform,Fintype.sum_prod_type,Fin.sum_univ_two,Real.negMulLog]
  simp only [one_div,Real.log_inv,h4]
  field_simp [show Real.log 2 ≠ 0 from (Real.log_pos (by norm_num)).ne']

lemma block_input : ent (pmask (G := BB) bMass) = 7/3 + Real.logb 2 3 := by
  have h12 : Real.log 12 = 2*Real.log 2 + Real.log 3 := by
    rw [show (12:ℝ)=2^2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]; norm_num
  have h24 : Real.log 24 = 3*Real.log 2 + Real.log 3 := by
    rw [show (24:ℝ)=2^3*3 by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]; norm_num
  norm_num [ent,pmask,bMass,uniform,Fintype.sum_prod_type,Fin.sum_univ_two,Real.negMulLog,Real.logb]
  simp only [one_div,Real.log_inv,h12,h24]
  field_simp [show Real.log 2 ≠ 0 from (Real.log_pos (by norm_num)).ne']
  ring

end RelayConcrete

namespace RelayDisproof
open RelayEntropy RelayMaskedLaw RelayAdderUpper RelayAdderCertificate RelayConcrete RelayFullObservation
  RelayCodeSimulation RelayRelabel OMA.S_itp_relay_channel
open scoped BigOperators Classical

variable {B G R T : Type} [Fintype B] [Fintype G] [Fintype R] [Fintype T] [AddGroup G]

lemma ent_bound (p : T → ℝ) (hp : ∀ t, 0 ≤ p t) :
    ent p ≤ Fintype.card T / Real.log 2 := by
  unfold ent
  calc
    _ ≤ ∑ _ : T, 1 / Real.log 2 := Finset.sum_le_sum (fun t _ =>
      div_le_div_of_nonneg_right ((Real.negMulLog_le_one_sub_self (hp t)).trans (by linarith [hp t]))
        (Real.log_pos (by norm_num)).le)
    _ = _ := by simp [div_eq_mul_inv]

lemma full_le_rate (adder : B → R → T) (hinj : ∀ r, Function.Injective (fun b => adder b r))
    (px : B × G → ℝ) (pr : R → ℝ) (hx : IsPmf px) (hr : IsPmf pr) :
    minimum (fullConstraints adder px pr (Fintype.equivFin (B × G))) ≤
      coverElGamalTheorem7Rate (maskedK (G := G) adder) := by
  let e := Fintype.equivFin (B × G)
  unfold coverElGamalTheorem7Rate
  apply le_csSup
  · refine ⟨(Fintype.card T : ℝ) / Real.log 2,?_⟩
    rintro s ⟨_,_,_,_,pq,pa,pu,pX,pR,pV,hq,ha,hu,hX,hR,hV,rfl⟩
    rw [catalogue_minimum,masked_constraints adder hinj _ _ _ _ _ _ hq ha hu hX hR hV]
    apply le_trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [condAdder adder _ _ _ _ _ hu hX hR]
    apply weighted_le _ _ _ _ hq ha
    intro q a
    apply ent_bound
    intro t
    unfold addLaw push
    exact Finset.sum_nonneg (fun br _ => by
      split_ifs
      · exact mul_nonneg ((bitLaw_pmf _ _ hu hX _).1 _) (hR.1 _ _)
      · exact le_rfl)
  · exact ⟨1,1,1,Fintype.card (B × G),single,fun _ => single,fun _ => single,fun _ => px,
      fun _ => pr,fun i => point (e i.2.2.1),single_pmf,single_kernel,single_kernel,
      ⟨fun _ => hx.1,fun _ => hx.2⟩,⟨fun _ => hr.1,fun _ => hr.2⟩,point_kernel _,rfl⟩

theorem single_witness :
    fullConstraints integerSum (pmask (G := Bit) (uniform Bit)) (uniform Bit)
      (Fintype.equivFin (Bit × Bit)) = (3/2,2,3/2) := by
  rw [full_constraints integerSum bit_adder_inj _ _ (pmask_pmf _ uniform_pmf) uniform_pmf,
    unmask,one_output,one_input]

/-- All three constraints at the four-strategy witness, in bits per pair. -/
theorem block_witness :
    fullConstraints adder₂ (pmask (G := BB) bMass) (uniform BB) (Fintype.equivFin (BB × BB)) =
    (11/6 + 3/4 * Real.logb 2 3, 7/3 + Real.logb 2 3, 11/6 + 3/4 * Real.logb 2 3) := by
  rw [full_constraints adder₂ adder₂_inj _ _ (pmask_pmf _ bMass_pmf) uniform_pmf,
    unmask,block_output,sumPair_entropy,block_input]

theorem single_exact : coverElGamalTheorem7Rate K = 3/2 := by
  apply le_antisymm one_use_upper
  have h := full_le_rate integerSum bit_adder_inj (pmask (G := Bit) (uniform Bit)) (uniform Bit)
    (pmask_pmf _ uniform_pmf) uniform_pmf
  rw [single_witness] at h
  norm_num [minimum] at h
  exact h

theorem block_lower : 11/6 + 3/4 * Real.logb 2 3 ≤ coverElGamalTheorem7Rate L := by
  have h := full_le_rate adder₂ adder₂_inj (pmask (G := BB) bMass) (uniform BB)
    (pmask_pmf _ bMass_pmf) uniform_pmf
  rw [block_witness] at h
  simpa only [minimum,min_eq_right (by linarith only [strict_gap] : 11/6 + 3/4 * Real.logb 2 3 ≤ 7/3 + Real.logb 2 3),min_self] using h

theorem block_strict : 3 < coverElGamalTheorem7Rate L := strict_gap.trans_le block_lower

theorem two_use_separation : 2 * coverElGamalTheorem7Rate K < coverElGamalTheorem7Rate L := by
  rw [single_exact]
  norm_num
  exact block_strict

lemma incompatible {X' R' Y' Z' : Type} [Fintype X'] [Fintype R'] [Fintype Y'] [Fintype Z']
    {W : X' × R' → Y' × Z' → ℝ} (sim : PairSim K W) (hW : IsKernel W)
    (h3W : 3 < coverElGamalTheorem7Rate W) (hyp : type_of% @OMA.S_itp_relay_channel.main) : False := by
  have cK : relayCapacity K = 3/2 := (of_universal hyp (masked_kernel (G := Bit) integerSum)).trans single_exact
  have cL : 3 < relayCapacity W := by
    rw [of_universal hyp hW]
    exact h3W
  have hbound : BddAbove {s : ℝ | IsRelayAchievable K s} := by
    by_contra hb
    rw [relayCapacity,csSup_of_not_bddAbove hb,Real.sSup_empty] at cK
    norm_num at cK
  have hne : Set.Nonempty {s : ℝ | IsRelayAchievable W s} := by
    by_contra he
    rw [relayCapacity,Set.not_nonempty_iff_eq_empty.mp he,Real.sSup_empty] at cL
    norm_num at cL
  obtain ⟨s,hs,h3⟩ := exists_lt_of_lt_csSup hne cL
  let v := (s+3)/4
  have hv : IsRelayAchievable K v := sim.achievable (masked_kernel (G := Bit) integerSum) (0,0) 0
    hs (by dsimp [v]; linarith) (by dsimp [v]; linarith)
  have hup : v ≤ relayCapacity K := le_csSup hbound hv
  rw [cK] at hup
  dsimp [v] at hup
  linarith

end RelayDisproof

namespace RelayPolicies
open RelayEntropy RelayMaskedLaw RelayAdderUpper RelayFullObservation RelayAdderCertificate RelayRelabel RelayConcrete
  RelayDisproof OMA.S_itp_relay_channel
open scoped BigOperators Classical
variable {Ω X R Y Z R' Q A U V D : Type} [Fintype Ω] [Fintype X] [Fintype R] [Fintype Y]
  [Fintype Z] [Fintype R'] [Fintype Q] [Fintype A] [Fintype U] [Fintype V] [Fintype D]

omit [Fintype X] in
lemma push_nn (p : Ω → ℝ) (hp : ∀ i, 0 ≤ p i) (f : Ω → X) (x : X) : 0 ≤ push f p x :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hp]

/-- Each conditional entropy is a weighted average of entropies on its output alphabet. -/
lemma CE_bounds [Nonempty X] (p : Ω → ℝ) (hp : IsPmf p) (x : Ω → X) (c : Ω → D) :
    0 ≤ CE p x c ∧ CE p x c ≤ Fintype.card X / Real.log 2 := by
  let m := push c p
  let j := push (fun i => (c i,x i)) p
  have hj (d : D) (b : X) : 0 ≤ j (d,b) := push_nn p hp.1 _ _
  have hs (d : D) : ∑ b, j (d,b) = m d := by
    unfold j m push
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases he : c i = d <;> simp [he]
  have hb (d : D) (b : X) : j (d,b) ≤ m d := hs d ▸ Finset.single_le_sum (fun b _ => hj d b) (Finset.mem_univ b)
  let k (d : D) (b : X) := if m d = 0 then uniform X b else j (d,b) / m d
  have hk (d : D) : IsPmf (k d) := by
    by_cases he : m d = 0
    · simpa [k,he] using (uniform_pmf (G := X))
    · constructor
      · intro b; simp only [k,if_neg he]; exact div_nonneg (hj d b) (push_nn p hp.1 c d)
      · simp [k,he,← Finset.sum_div,hs]
  have hd (d : D) (b : X) : j (d,b) = m d * k d b := by
    by_cases he : m d = 0
    · have := hb d b; have := hj d b; simp [he]; linarith
    · simp only [k,if_neg he]; field_simp
  have hav : CE p x c = ∑ d, m d * ent (k d) := by
    rw [CE,H_extend p c x k (fun d => (hk d).2) hd,add_sub_cancel_left]
  have hn (d : D) : 0 ≤ ent (k d) := by
    apply Finset.sum_nonneg
    intro b _
    have h1 : k d b ≤ 1 := (hk d).2 ▸ Finset.single_le_sum (fun b _ => (hk d).1 b) (Finset.mem_univ b)
    exact div_nonneg (Real.negMulLog_nonneg ((hk d).1 b) h1) (Real.log_pos (by norm_num)).le
  rw [hav]
  refine ⟨Finset.sum_nonneg fun d _ => mul_nonneg (push_nn _ hp.1 c d) (hn d),?_⟩
  calc
    _ ≤ ∑ d, m d * (Fintype.card X / Real.log 2) :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (ent_bound _ (hk d).1) (push_nn _ hp.1 c d)
    _ = _ := by rw [← Finset.sum_mul, show ∑ d, m d = 1 from (push_total p c).trans hp.2,one_mul]

lemma joint_pmf (K : X × R → Y × Z → ℝ) (pq : Q → ℝ) (pa : Q → A → ℝ)
    (pu : A × Q → U → ℝ) (px : U × Q → X → ℝ) (pr : A × Q → R → ℝ) (pv : U × R × Z × Q → V → ℝ)
    (hK : IsKernel K) (hq : IsPmf pq) (ha : IsKernel pa) (hu : IsKernel pu)
    (hx : IsKernel px) (hr : IsKernel pr) (hv : IsKernel pv) :
    IsPmf (thm7Joint K pq pa pu px pr pv) := by
  constructor
  · rintro ⟨q,a,u,x,r,y,z,v⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (hq.1 _) (ha.1 _ _)) (hu.1 _ _)) (hx.1 _ _)) (hr.1 _ _)) (hK.1 _ _)) (hv.1 _ _)
  · have ht (x : X) (r : R) : ∑ y, ∑ z, K (x,r) (y,z) = 1 := by
      simpa [Fintype.sum_prod_type] using hK.2 (x,r)
    simp [thm7Joint,Fintype.sum_prod_type,← Finset.mul_sum,hv.2,ht,hr.2,hx.2,hu.2,ha.2,hq.2]

lemma candidate_bound [Nonempty X] [Nonempty Z] (p : Q × A × U × X × R × Y × Z × V → ℝ)
    (hp : IsPmf p) : thm7MinRate p ≤ Fintype.card X / Real.log 2 + Fintype.card Z / Real.log 2 := by
  rw [catalogue_minimum]
  apply le_trans ((min_le_right _ _).trans (min_le_left _ _))
  let x (t : Q × A × U × X × R × Y × Z × V) := t.2.2.2.1
  let z (t : Q × A × U × X × R × Y × Z × V) := t.2.2.2.2.2.2.1
  change MI p x (fun t => (t.2.2.2.2.2.2.2,t.2.2.2.2.2.1)) (fun t => (t.2.2.1,t.2.2.2.2.1,t.1)) +
    MI p (fun t => t.2.2.1) z (fun t => (t.2.1,t.2.2.2.2.1,t.1)) ≤ _
  rw [MI_left,MI_eq p _ z]
  apply add_le_add
  · exact (sub_le_self _ (CE_bounds p hp x
      (fun t => ((t.2.2.1,t.2.2.2.2.1,t.1),t.2.2.2.2.2.2.2,t.2.2.2.2.2.1))).1).trans
      (CE_bounds p hp x (fun t => (t.2.2.1,t.2.2.2.2.1,t.1))).2
  · exact (sub_le_self _ (CE_bounds p hp z (fun t => ((t.2.1,t.2.2.2.2.1,t.1),t.2.2.1))).1).trans
      (CE_bounds p hp z (fun t => (t.2.1,t.2.2.2.2.1,t.1))).2

def changeRelay (g : R → R') (t : RelayRelabel.Row Q A U X R Y Z V) : RelayRelabel.Row Q A U X R' Y Z V :=
  (t.1,t.2.1,t.2.2.1,t.2.2.2.1,g t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2.1,t.2.2.2.2.2.2.2)

lemma map_min (g : R → R') (hg : Function.Injective g) (p : RelayRelabel.Row Q A U X R Y Z V → ℝ) :
    thm7MinRate (push (changeRelay g) p) = thm7MinRate p := by
  rw [catalogue_minimum,catalogue_minimum]
  apply congrArg minimum
  unfold changeRelay
  rw [three_push]
  unfold rowThree three
  repeat' first
    | (apply MI_equiv <;> intro i j <;> solve | simp only [Prod.mk.injEq,hg.eq_iff])
    | apply congrArg₂ Prod.mk
    | apply congrArg₂ HSub.hSub
    | apply congrArg₂ HAdd.hAdd

omit [Fintype R'] in
lemma embedded_joint (g : R → R') (ret : R' → R) (hret : Function.LeftInverse ret g)
    (L : X × R → Y × Z → ℝ) (W : X × R' → Y × Z → ℝ) (he : ∀ x r, W (x,g r) = L (x,r))
    (pq : Q → ℝ) (pa : Q → A → ℝ) (pu : A × Q → U → ℝ)
    (px : U × Q → X → ℝ) (pr : A × Q → R → ℝ) (pv : U × R × Z × Q → V → ℝ) :
    thm7Joint W pq pa pu px (fun i => push g (pr i)) (fun i => pv (i.1,ret i.2.1,i.2.2.1,i.2.2.2)) =
      push (changeRelay g) (thm7Joint L pq pa pu px pr pv) := by
  have hmap : Function.Injective (changeRelay (Q:=Q) (A:=A) (U:=U) (X:=X) (Y:=Y) (Z:=Z) (V:=V) g) := by
    rintro ⟨q,a,u,x,r,y,z,v⟩ ⟨q',a',u',x',r',y',z',v'⟩
    simp [changeRelay,hret.injective.eq_iff]
  funext ⟨q,a,u,x,s,y,z,v⟩
  by_cases h : ∃ r, g r=s
  · obtain ⟨r,rfl⟩ := h
    change _ = push (changeRelay g) _ (changeRelay g (q,a,u,x,r,y,z,v))
    simp only [push,hmap.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp [thm7Joint,push,hret.injective.eq_iff,hret r,he]
  · have hf (r) : g r ≠ s := fun hr => h ⟨r,hr⟩
    have hn (t : RelayRelabel.Row Q A U X R Y Z V) : changeRelay g t ≠ (q,a,u,x,s,y,z,v) :=
      fun ht => hf _ (congrArg (fun w : RelayRelabel.Row Q A U X R' Y Z V => w.2.2.2.2.1) ht)
    simp [thm7Joint,push,hf,hn]

abbrev Policy := Bit × (Observation → Bit)

def allOut (x : BB × BB) (s : Policy) (n : BB) : (TT × BB) × (BB × BB) :=
  (((integerSum x.1.1 s.1,integerSum x.1.2 (s.2 (x.1.1,n.1))),x.2+n),(x.1,n))

noncomputable def BK (i : (BB × BB) × Policy) := push (allOut i.1 i.2) (uniform BB)

lemma BK_kernel : IsKernel BK :=
  ⟨fun _ _ => push_nn _ uniform_pmf.1 _ _,fun _ => (push_total _ _).trans uniform_total⟩

lemma BK_value (x : BB × BB) (s : Policy) (y : TT × BB) (z : BB × BB) :
    BK (x,s) (y,z) = if allOut x s z.2 = (y,z) then uniform BB z.2 else 0 := by
  unfold BK push
  calc
    _ = _ := Finset.sum_eq_single z.2 (fun n _ hn => if_neg (fun h => hn
      (congrArg (fun o : (TT × BB) × (BB × BB) => o.2.2) h))) (by simp)
    _ = _ := by by_cases h : allOut x s z.2 = (y,z) <;> simp [h]

/-- Each of the 32 deterministic policies executes as two strictly causal uses of K. -/
def allSim : RelayCodeSimulation.PairSim K BK where
  src := transpose
  dest := transpose
  obs := transpose
  first := Prod.fst
  next := Prod.snd
  factor := by
    rintro ⟨⟨b₁,b₂⟩,⟨m₁,m₂⟩⟩ ⟨r,h⟩ ⟨⟨t₁,t₂⟩,⟨d₁,d₂⟩⟩ ⟨⟨o₁,o₂⟩,⟨n₁,n₂⟩⟩
    simp only [K,BK_value,allOut,masked_value,maskedOut,transpose,Equiv.coe_fn_mk,Prod.mk.injEq]
    by_cases he : b₁=o₁
    · subst o₁
      by_cases hb : b₂=o₂
      · subst o₂
        simp only [and_true,uniform,Fintype.card_prod,Fintype.card_fin]
        split_ifs <;> simp_all
        norm_num
      · simp [hb]
    · simp [he]

def policy (s : BB) : Policy := (s.1,secondInput s.1 s.2)
def readPolicy (s : Policy) : BB := (s.1,s.2 (s.1,0))

lemma read_policy : Function.LeftInverse readPolicy policy := by
  rintro ⟨r,j⟩
  simp [readPolicy,policy,secondInput]

/-- The unrestricted two-use alphabet contains every first input and every causal response. -/
theorem unrestricted_lower : 11/6 + 3/4 * Real.logb 2 3 ≤ coverElGamalTheorem7Rate BK := by
  let pm := pmask (G:=BB) bMass
  let e := Fintype.equivFin (BB × BB)
  let pv (i : Tiny × BB × (BB × BB) × Tiny) := point (e i.2.2.1)
  let J := thm7Joint L single (fun _ => single) (fun _ => single) (fun _ => pm)
    (fun _ => uniform BB) pv
  have hh : thm7MinRate J = 11/6 + 3/4 * Real.logb 2 3 := by
    change minimum (fullConstraints adder₂ _ _ _) = _
    rw [block_witness]
    exact min_eq_left (le_min (by linarith only [strict_gap]) le_rfl)
  rw [← hh]
  unfold coverElGamalTheorem7Rate
  apply le_csSup
  · refine ⟨Fintype.card (BB × BB) / Real.log 2 + Fintype.card (BB × BB) / Real.log 2,?_⟩
    rintro r ⟨_,_,_,_,pq,pa,pu,px,pr,v,hq,ha,hu,hx,hr,hv,rfl⟩
    exact candidate_bound _ (joint_pmf _ _ _ _ _ _ _ BK_kernel hq ha hu hx hr hv)
  · refine ⟨1,1,1,Fintype.card (BB × BB),single,fun _ => single,fun _ => single,fun _ => pm,
      (fun _ => push policy (uniform BB)),(fun i => pv (i.1,readPolicy i.2.1,i.2.2.1,i.2.2.2)),
      single_pmf,single_kernel,single_kernel,⟨fun _ => (pmask_pmf _ bMass_pmf).1,fun _ => (pmask_pmf _ bMass_pmf).2⟩,
      ⟨fun _ _ => push_nn _ uniform_pmf.1 _ _,fun _ => (push_total _ _).trans uniform_total⟩,
      ⟨fun i => (point_kernel (fun i : Tiny × BB × (BB × BB) × Tiny => e i.2.2.1)).1 _,fun i =>
        (point_kernel (fun i : Tiny × BB × (BB × BB) × Tiny => e i.2.2.1)).2 _⟩,?_⟩
    rw [embedded_joint policy readPolicy read_policy L BK (fun _ _ => rfl) single (fun _ => single)
      (fun _ => single) (fun _ => pm) (fun _ => uniform BB) pv,map_min policy read_policy.injective]

theorem unrestricted_separation : 2 * coverElGamalTheorem7Rate K < coverElGamalTheorem7Rate BK := by
  rw [single_exact]
  exact lt_of_eq_of_lt (by norm_num : 2*(3/2:ℝ)=3) (strict_gap.trans_le unrestricted_lower)

end RelayPolicies

theorem OMA.disproof : ¬ (type_of% @OMA.S_itp_relay_channel.main) :=
  RelayDisproof.incompatible RelayPolicies.allSim RelayPolicies.BK_kernel
    (RelayAdderCertificate.strict_gap.trans_le RelayPolicies.unrestricted_lower)
