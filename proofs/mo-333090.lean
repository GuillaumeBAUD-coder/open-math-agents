import OMAStatements.S_mo_333090
import Mathlib

/-!
# Irrational numbers with coprime radix truncations

A finite walk eventually stays among states that recur arbitrarily late. If there
is no recurrent branching, each such state determines its next digit, so two
visits to the same state have equal digit tails. This forces the real to be rational.

Conversely, a branching state has two return words U and V with different first
digits. The concatenations UV and VU have equal length and encode arbitrary
binary streams. Every block contains a nonmaximal digit, so truncating the real
recovers its digit stream uniquely. Cantor's diagonal argument supplies an
irrational value in this family. Shifting its integral part matches the initial
residue and preserves the allowed unit walk at every truncation.
-/

namespace Mo333090Proof

open OMA.S_mo_333090 Filter

private lemma walk_reaches {k M : ℕ} (s : ℕ → Fin M) (d : ℕ → Fin k)
    (hw : ∀ n, edge k M (s n) (d n) (s (n+1))) {i j : ℕ} (hij : i ≤ j) :
    reaches k M (s i) (s j) := by
  intro T hi hT
  induction j,hij using Nat.le_induction with
  | base => exact hi
  | succ j _ h => exact hT _ h _ _ (hw j)

private lemma eventual_recurrence {V : Type*} [Finite V] (s : ℕ → V) :
    ∃ N, ∀ n ≥ N, ∀ m, ∃ t ≥ m, s t = s n := by
  classical
  have h (v : V) : ∀ᶠ n : ℕ in atTop, s n = v → ∃ᶠ t : ℕ in atTop, s t = v := by
    by_cases hv : ∃ᶠ t : ℕ in atTop, s t = v
    · exact Eventually.of_forall fun _ _ => hv
    · have he : ∀ᶠ n : ℕ in atTop, ¬ s n = v := not_frequently.mp hv
      exact he.mono fun n hn hh => False.elim (hn hh)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_all.mpr h)
  exact ⟨N,fun n hn => frequently_atTop.mp (hN n hn (s n) rfl)⟩

/-- A walk in the absence of any recurrent branching repeats an entire digit tail. -/
theorem equal_tails_of_no_branch {k M : ℕ} (s : ℕ → Fin M) (d : ℕ → Fin k)
    (hw : ∀ n, edge k M (s n) (d n) (s (n+1))) (hb : ¬ branching k M) :
    ∃ i j : ℕ, i < j ∧ ∀ t : ℕ, d (i+t) = d (j+t) := by
  obtain ⟨N,hN⟩ := eventual_recurrence s
  have unique {i j : ℕ} (hi : N ≤ i) (hj : N ≤ j) (he : s i = s j) : d i = d j := by
    by_contra hd
    obtain ⟨ti,hti,hsi⟩ := hN i hi (i+1)
    obtain ⟨tj,htj,hsj⟩ := hN j hj (j+1)
    have hri := walk_reaches s d hw hti
    have hrj := walk_reaches s d hw htj
    rw [hsi] at hri
    rw [hsj,←he] at hrj
    exact hb ⟨s i,s (i+1),s (j+1),d i,d j,hd,hw i,hri,he ▸ hw j,hrj⟩
  obtain ⟨j,hj,he⟩ := hN N le_rfl (N+1)
  have hr (t : ℕ) : s (N+t) = s (j+t) := by
    induction t with
    | zero => simpa using he.symm
    | succ t ih =>
      have hd := unique (Nat.le_add_right N t) (by omega : N ≤ j+t) ih
      have hp := (hw (N+t)).2.2
      have hq := (hw (j+t)).2.2
      apply Fin.ext
      rw [ih,hd] at hp
      exact hp.symm.trans hq
  exact ⟨N,j,by omega,fun t => unique (Nat.le_add_right N t) (by omega) (hr t)⟩

end Mo333090Proof

namespace Mo333090Path
open OMA.S_mo_333090

private structure Walk {k M : ℕ} (s t : Fin M) where
  len : ℕ
  digit : ℕ → Fin k
  state : ℕ → Fin M
  start : state 0 = s
  finish : state len = t
  valid : ∀ n, n < len → edge k M (state n) (digit n) (state (n+1))

private def stay {k M : ℕ} (s : Fin M) (d : Fin k) : Walk (k:=k) s s :=
  ⟨0, fun _ => d, fun _ => s, rfl,rfl,fun _ h => (Nat.not_lt_zero _ h).elim⟩

private def step {k M : ℕ} {s t : Fin M} {d : Fin k} (h : edge k M s d t) :
    Walk (k:=k) s t :=
  ⟨1, fun _ => d, fun n => if n=0 then s else t, by simp, by simp, by
    intro n hn
    obtain rfl : n=0 := by omega
    simpa using h⟩

private def cat {k M : ℕ} {s t u : Fin M} (p : Walk (k:=k) s t) (q : Walk (k:=k) t u) :
    Walk (k:=k) s u where
  len := p.len+q.len
  digit n := if n < p.len then p.digit n else q.digit (n-p.len)
  state n := if n < p.len then p.state n else q.state (n-p.len)
  start := by
    split_ifs with h
    · exact p.start
    · have hz : p.len = 0 := by omega
      simpa [hz] using q.start.trans (p.finish.symm.trans (by rw [hz,p.start]))
  finish := by simp [q.finish]
  valid n hn := by
    by_cases hp : n < p.len
    · simp only [if_pos hp]
      by_cases hp' : n+1 < p.len
      · simpa only [if_pos hp'] using p.valid n hp
      · have he : n+1=p.len := by omega
        simp only [he, Nat.lt_irrefl, if_false, Nat.sub_self, q.start]
        simpa only [he,p.finish] using p.valid n hp
    · have hp' : ¬ n+1 < p.len := by omega
      have hinc : n+1-p.len=(n-p.len)+1 := by omega
      simp only [if_neg hp,if_neg hp',hinc]
      exact q.valid _ (by omega)

private theorem walk_of_reaches {k M : ℕ} {s t : Fin M} (d : Fin k)
    (h : reaches k M s t) : Nonempty (Walk (k:=k) s t) := by
  classical
  let allowed := Finset.univ.filter (fun v : Fin M => Nonempty (Walk (k:=k) s v))
  have hm (v : Fin M) : v ∈ allowed ↔ Nonempty (Walk (k:=k) s v) := by simp [allowed]
  apply (hm t).mp
  apply h allowed ((hm s).mpr ⟨stay s d⟩)
  intro u hu e v he
  obtain ⟨w⟩ := (hm u).mp hu
  exact (hm v).mpr ⟨cat w (step he)⟩

private theorem weave {k M : ℕ} (s : Fin M) (W : Bool → Walk (k:=k) s s)
    (m : ℕ) (hm : 0 < m) (hlen : ∀ b, (W b).len=m)
    (hinj : Function.Injective (fun b => (W b).digit 0))
    (hlo : ∀ b, ∃ i < m, ((W b).digit i).val+1 < k) :
    ∃ (D : (ℕ → Bool) → ℕ → Fin k) (S : (ℕ → Bool) → ℕ → Fin M),
      Function.Injective D ∧ ∀ c, S c 0=s ∧
      (∀ n, edge k M (S c n) (D c n) (S c (n+1))) ∧
      ∀ n, ∃ j ≥ n, (D c j).val+1 < k := by
  let D (c : ℕ → Bool) (n : ℕ) := (W (c (n/m))).digit (n%m)
  let S (c : ℕ → Bool) (n : ℕ) := (W (c (n/m))).state (n%m)
  have enc (c : ℕ → Bool) (q i : ℕ) (hi : i < m) :
      D c (i+q*m) = (W (c q)).digit i := by
    simp [D, Nat.add_mul_div_right, hm, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
  refine ⟨D,S,?_,fun c => ⟨by simp [S,Walk.start],?_,?_⟩⟩
  · intro c e h
    funext n
    apply hinj
    have he := congrFun h (0+n*m)
    rwa [enc c n 0 hm,enc e n 0 hm] at he
  · intro n
    have hmod := Nat.mod_lt n hm
    have h := (W (c (n/m))).valid (n%m) (by rw [hlen]; exact hmod)
    change edge k M _ _ ((W (c ((n+1)/m))).state ((n+1)%m))
    have hrep : (n+1)%m = (n%m+1)%m := by
      exact (Nat.mod_add_mod n m 1).symm
    by_cases hi : n%m+1 < m
    · have he := hrep.trans (Nat.mod_eq_of_lt hi)
      have hdiv : (n+1)/m=n/m := Nat.succ_div_of_mod_ne_zero (by omega)
      rw [he,hdiv]
      exact h
    · have he : n%m+1=m := by omega
      have hz : (n+1)%m=0 := by rw [hrep,he,Nat.mod_self]
      rw [hz,Walk.start]
      have hf : (W (c (n/m))).state (n%m+1) = s := by
        have hlocal := he.trans (hlen (c (n/m))).symm
        exact (congrArg (W (c (n/m))).state hlocal).trans (W _).finish
      rw [hf] at h
      exact h
  · intro n
    obtain ⟨i,hi,hd⟩ := hlo (c n)
    exact ⟨i+n*m,by have := Nat.le_mul_of_pos_right n hm; omega, by rwa [enc c n i hi]⟩

theorem branching_streams {k M : ℕ} (hb : branching k M) :
    ∃ (s : Fin M) (D : (ℕ → Bool) → ℕ → Fin k) (S : (ℕ → Bool) → ℕ → Fin M),
      Function.Injective D ∧ ∀ c, S c 0=s ∧
      (∀ n, edge k M (S c n) (D c n) (S c (n+1))) ∧
      ∀ n, ∃ j ≥ n, (D c j).val+1 < k := by
  obtain ⟨s,u,v,d,e,hne,hsu,hus,hsv,hvs⟩ := hb
  obtain ⟨ru⟩ := walk_of_reaches d hus
  obtain ⟨rv⟩ := walk_of_reaches e hvs
  let U := cat (step hsu) ru
  let V := cat (step hsv) rv
  have hu : 0 < U.len := by dsimp [U,cat,step]; omega
  have hv : 0 < V.len := by dsimp [V,cat,step]; omega
  have ud : U.digit 0 = d := rfl
  have ve : V.digit 0 = e := rfl
  let W : Bool → Walk (k:=k) s s := fun b => if b then cat V U else cat U V
  let m := U.len+V.len
  have h0 : (W false).digit 0=d := by simpa [W,cat,hu] using ud
  have h1 : (W true).digit 0=e := by simpa [W,cat,hv] using ve
  have hUV : (W false).digit U.len=e := by simpa [W,cat] using ve
  have hVU : (W true).digit V.len=d := by simpa [W,cat] using ud
  refine ⟨s,?_⟩
  apply weave s W m (by dsimp [m]; omega)
  · intro b; cases b <;> simp [W,cat,m,Nat.add_comm]
  · intro b c H
    cases b <;> cases c <;> simp_all
  · have hdiff : d.val ≠ e.val := fun h => hne (Fin.ext h)
    have hsmall : d.val+1<k ∨ e.val+1<k := by have := d.isLt; have := e.isLt; omega
    intro b
    cases b
    · rcases hsmall with hd|he
      · exact ⟨0,by dsimp [m]; omega,by rwa [h0]⟩
      · exact ⟨U.len,by dsimp [m]; omega,by rwa [hUV]⟩
    · rcases hsmall with hd|he
      · exact ⟨V.len,by dsimp [m]; omega,by rwa [hVU]⟩
      · exact ⟨0,by dsimp [m]; omega,by rwa [h1]⟩

end Mo333090Path

namespace Mo333090Radix

def wordPrefix {k : ℕ} (D : ℕ → Fin k) : ℕ → ℕ
  | 0 => 0
  | n+1 => k * wordPrefix D n + (D n).val

private theorem shift_one {k : ℕ} (hk : 1 < k) (D : ℕ → Fin k) :
    (k:ℝ)*Real.ofDigits D = (D 0).val + Real.ofDigits (fun i => D (1+i)) := by
  have h := Real.ofDigits_eq_sum_add_ofDigits D 1
  simp only [Finset.sum_range_one, Real.ofDigitsTerm, zero_add, pow_one] at h
  rw [h]
  have hne : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp
  rw [show (fun i => D (i+1)) = (fun i => D (1+i)) by funext i; rw [Nat.add_comm]]

theorem scaled_ofDigits {k : ℕ} (hk : 1 < k) (D : ℕ → Fin k) (n : ℕ) :
    (k:ℝ)^n * Real.ofDigits D = (wordPrefix D n : ℝ) + Real.ofDigits (fun i => D (n+i)) := by
  induction n with
  | zero => simp [wordPrefix]
  | succ n ih =>
    have e := shift_one hk (fun i => D (n+i))
    simp only [Nat.add_zero, ← Nat.add_assoc] at e
    rw [pow_succ', mul_assoc, ih, mul_add, e, wordPrefix, Nat.cast_add, Nat.cast_mul]
    ring

private theorem strict_ofDigits {k : ℕ} (hk : 1 < k) (D : ℕ → Fin k)
    (hD : ∃ i, (D i).val + 1 < k) : Real.ofDigits D < 1 := by
  let last : Fin k := ⟨k-1, by omega⟩
  let E (_ : ℕ) := last
  have hlast : Real.ofDigits E = 1 := Real.ofDigits_const_last_eq_one' hk
  rw [← hlast]
  obtain ⟨i,hi⟩ := hD
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply Summable.tsum_lt_tsum (i := i) _ _ Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm
  · intro j
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Nat.cast_le.mpr (show (D j).val ≤ (E j).val by have := (D j).isLt; dsimp [E,last]; omega)
  · apply mul_lt_mul_of_pos_right _ (by positivity)
    exact Nat.cast_lt.mpr (show (D i).val < (E i).val by dsimp [E,last]; omega)

theorem floor_ofDigits_prefix {k : ℕ} (hk : 1 < k) (D : ℕ → Fin k)
    (hD : ∀ n, ∃ j ≥ n, (D j).val + 1 < k) (n : ℕ) :
    ⌊(k:ℝ)^n * Real.ofDigits D⌋₊ = wordPrefix D n := by
  rw [scaled_ofDigits hk]
  have h₀ := Real.ofDigits_nonneg (fun i => D (n+i))
  have h₁ : Real.ofDigits (fun i => D (n+i)) < 1 := by
    apply strict_ofDigits hk
    obtain ⟨j,hj,hd⟩ := hD n
    exact ⟨j-n, by simpa only [Nat.add_sub_of_le hj] using hd⟩
  exact (Nat.floor_eq_iff (by positivity)).mpr ⟨by linarith,by linarith⟩

theorem ofDigits_injective {k : ℕ} (hk : 1 < k) (D E : ℕ → Fin k)
    (hD : ∀ n, ∃ j ≥ n, (D j).val+1 < k) (hE : ∀ n, ∃ j ≥ n, (E j).val+1 < k)
    (he : Real.ofDigits D = Real.ofDigits E) : D = E := by
  have eqn (n : ℕ) : wordPrefix D n = wordPrefix E n := by
    rw [← floor_ofDigits_prefix hk D hD, ← floor_ofDigits_prefix hk E hE, he]
  funext n
  apply Fin.ext
  have h := eqn (n+1)
  simpa only [wordPrefix,eqn n,Nat.add_right_inj] using h

noncomputable def inputDigits {k : ℕ} (hk : 1 < k) (x : ℝ) (n : ℕ) : Fin k :=
  ⟨⌊(k:ℝ)^(n+1)*x⌋₊ % k, Nat.mod_lt _ (by omega)⟩

theorem not_irrational_of_equal_tails {k : ℕ} (hk : 1 < k) (x : ℝ) (hx : 0 < x)
    {i j : ℕ} (hij : i < j)
    (ht : ∀ t, inputDigits hk x (i+t) = inputDigits hk x (j+t)) : ¬ Irrational x := by
  let : NeZero k := ⟨by omega⟩
  let q (n : ℕ) := ⌊(k:ℝ)^n*x⌋₊
  let f (n : ℕ) := (k:ℝ)^n*x - q n
  have hf (n : ℕ) : f n ∈ Set.Ico 0 1 := by
    change 0 ≤ (k:ℝ)^n*x - q n ∧ (k:ℝ)^n*x - q n < 1
    exact ⟨sub_nonneg.mpr (Nat.floor_le (by positivity)),
      by have h := Nat.lt_floor_add_one ((k:ℝ)^n*x); dsimp [q]; linarith⟩
  have digit (n t : ℕ) : inputDigits hk x (n+t) = Real.digits (f n) k t := by
    apply Fin.ext
    change ⌊(k:ℝ)^(n+t+1)*x⌋₊ % k = ⌊f n * (k:ℝ)^(t+1)⌋₊ % k
    have e : (k:ℝ)^(n+t+1)*x = f n * (k:ℝ)^(t+1) + ((q n * k^(t+1) : ℕ):ℝ) := by
      dsimp [f]
      push_cast
      rw [Nat.add_assoc, pow_add]
      ring
    rw [e, Nat.floor_add_natCast (mul_nonneg (hf n).1 (by positivity)), pow_succ k t,
      ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
  have he : f i = f j := by
    rw [← Real.ofDigits_digits hk (hf i), ← Real.ofDigits_digits hk (hf j)]
    apply congrArg Real.ofDigits
    funext t
    rw [← digit, ← digit, ht]
  have hpow : k^i < k^j := Nat.pow_lt_pow_right hk hij
  intro hirr
  apply (irrational_iff_ne_rational x).mp hirr
    ((q j:ℤ) - q i) (((k^j:ℕ):ℤ) - (k^i:ℕ)) (by exact sub_ne_zero.mpr (by exact_mod_cast hpow.ne'))
  push_cast
  apply (eq_div_iff (sub_ne_zero.mpr (by exact_mod_cast hpow.ne'))).mpr
  dsimp only [f] at he
  linarith only [he]

end Mo333090Radix

namespace Mo333090Proof

open OMA.S_mo_333090

noncomputable def truncation (k : ℕ) (x : ℝ) (n : ℕ) := ⌊(k:ℝ)^n*x⌋₊

theorem prefix_succ {k : ℕ} (hk : 1<k) (x : ℝ) (n : ℕ) :
    truncation k x (n+1) = k*truncation k x n + truncation k x (n+1)%k := by
  have h := Nat.cast_mul_floor_div_cancel (by omega : k ≠ 0) ((k:ℝ)^n*x)
  have h' : truncation k x (n+1) / k = truncation k x n := by
    simpa only [truncation,pow_succ',mul_assoc] using h
  have hdiv := Nat.mod_add_div (truncation k x (n+1)) k
  rw [h'] at hdiv
  omega

private theorem prefix_mod_coprime (m M : ℕ) (h : m.Coprime M) : (m%M).Coprime M := by
  change (m%M).gcd M = 1
  rw [(Nat.mod_modEq _ _).gcd_eq]
  exact h

/-- The fractional digits following level one form a walk among the unit residues. -/
theorem prefix_walk {k M : ℕ} (hk : 1<k) (hM : 0<M) (x : ℝ)
    (hp : ∀ n : ℕ, 0<n → (truncation k x n).Coprime M) :
    ∃ s : ℕ → Fin M, ∀ n, edge k M (s n)
      (⟨truncation k x (n+2)%k,Nat.mod_lt _ (by omega)⟩ : Fin k) (s (n+1)) := by
  let s (n : ℕ) : Fin M := ⟨truncation k x (n+1)%M,Nat.mod_lt _ hM⟩
  refine ⟨s,fun n => ⟨prefix_mod_coprime _ _ (hp _ (by omega)),prefix_mod_coprime _ _ (hp _ (by omega)),?_⟩⟩
  have h := ((Nat.mod_modEq (truncation k x (n+1)) M).mul_left k).add_right (truncation k x (n+2)%k)
  change (k*(truncation k x (n+1)%M) + truncation k x (n+2)%k)%M = truncation k x (n+2)%M
  exact h.trans (congrArg (fun v => v%M) (prefix_succ hk x (n+1)).symm)

/-- An injection of all binary streams into the reals has an irrational value. -/
theorem irrational_in_streams (f : (ℕ → Bool) → ℝ) (hf : Function.Injective f) :
    ∃ b, Irrational (f b) := by
  classical
  by_contra! h
  have hrat (b) : ∃ r : ℚ, (r:ℝ)=f b := Classical.not_not.mp (h b)
  choose g hg using hrat
  have hginj : Function.Injective g := by
    intro b c he
    exact hf ((hg b).symm.trans ((congrArg (fun r : ℚ => (r:ℝ)) he).trans (hg c)))
  let : Countable (ℕ → Bool) := hginj.countable
  obtain ⟨e,he⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n,hn⟩ := he (fun i => !(e i i))
  have hd := congrFun hn n
  cases hb : e n n <;> simp [hb] at hd

theorem shift_prefix {k : ℕ} (D : ℕ → Fin k) (B n : ℕ) :
    truncation k ((B:ℝ)+Real.ofDigits D) n = k^n*B + truncation k (Real.ofDigits D) n := by
  unfold truncation
  rw [mul_add,add_comm ((k:ℝ)^n*B),←Nat.cast_pow,←Nat.cast_mul,Nat.floor_add_natCast (mul_nonneg (Nat.cast_nonneg _) (Real.ofDigits_nonneg D)),add_comm]

/-- Any stream whose real evaluation obeys the digit recurrence gives the required
coprime prefixes after an integral shift into its initial state. -/
theorem realize_walk {k M : ℕ} (hM : 0<M) (D : ℕ → Fin k) (s : ℕ → Fin M)
    (hw : ∀ n, edge k M (s n) (D n) (s (n+1)))
    (hz : truncation k (Real.ofDigits D) 0 = 0)
    (hrec : ∀ n, truncation k (Real.ofDigits D) (n+1) = k*truncation k (Real.ofDigits D) n + (D n).val)
    (hI : Irrational (Real.ofDigits D)) :
    ∃ x : ℝ, 0 < x ∧ Irrational x ∧ ∀ n : ℕ, 0<n → (truncation k x n).Coprime M := by
  let B := (s 0).val + M
  let x := (B:ℝ)+Real.ofDigits D
  have hB : 0 < B := by dsimp [B]; omega
  refine ⟨x,add_pos_of_pos_of_nonneg (by exact_mod_cast hB) (Real.ofDigits_nonneg _),hI.natCast_add B,?_⟩
  have hmod (n : ℕ) : (truncation k x n)%M = (s n).val := by
    rw [shift_prefix]
    induction n with
    | zero => simp [hz,B,Nat.mod_eq_of_lt (s 0).isLt]
    | succ n ih =>
      have h := ((show k^n*B + truncation k (Real.ofDigits D) n ≡ (s n).val [MOD M] from
        ih.trans (Nat.mod_eq_of_lt (s n).isLt).symm).mul_left k).add_right (D n).val
      rw [pow_succ',hrec]
      rw [show k*k^n*B+(k*truncation k (Real.ofDigits D) n+(D n).val) =
        k*(k^n*B+truncation k (Real.ofDigits D) n)+(D n).val by ring]
      exact Eq.trans h (hw n).2.2
  intro n _
  have he : truncation k x n ≡ (s n).val [MOD M] := (hmod n).trans (Nat.mod_eq_of_lt (s n).isLt).symm
  change (truncation k x n).gcd M = 1
  rw [he.gcd_eq]
  exact (hw n).1

end Mo333090Proof

open OMA.S_mo_333090 Mo333090Proof Mo333090Path Mo333090Radix in
theorem OMA.solution : type_of% @OMA.S_mo_333090.main := by
  intro k M hk _ hM
  have hb : 1 < k := by omega
  constructor
  · rintro ⟨x,hx,hirr,hp⟩
    by_contra hno
    obtain ⟨s,hs⟩ := prefix_walk hb hM x hp
    let d (n : ℕ) := inputDigits hb x (n+1)
    obtain ⟨i,j,hij,ht⟩ := equal_tails_of_no_branch s d hs hno
    apply not_irrational_of_equal_tails hb x hx (Nat.succ_lt_succ hij) _ hirr
    intro t
    simpa only [d, Nat.succ_add] using ht t
  · intro hbranch
    obtain ⟨_,D,S,hD,hS⟩ := branching_streams hbranch
    have hfun : Function.Injective (fun c => Real.ofDigits (D c)) := by
      intro b c h
      exact hD (ofDigits_injective hb _ _ (hS b).2.2 (hS c).2.2 h)
    obtain ⟨b,hirr⟩ := irrational_in_streams _ hfun
    have hf (n : ℕ) : truncation k (Real.ofDigits (D b)) n = wordPrefix (D b) n :=
      floor_ofDigits_prefix hb _ (hS b).2.2 n
    exact realize_walk hM (D b) (S b) (hS b).2.1 (hf 0) (fun n => by rw [hf,hf]; rfl) hirr
