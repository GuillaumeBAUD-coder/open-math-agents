import FormalConjectures.ErdosProblems.«326»

namespace Cassels

-- At dyadic scale d, use multiples of d and d+1 between d² and 16d².
def grid (n : ℕ) : Prop :=
  n < 4 ∨ ∃ k : ℕ, let d := 2 ^ k; d^2 ≤ n ∧ n ≤ 16*d^2 ∧ (d ∣ n ∨ d+1 ∣ n)

lemma cover (n : ℕ) : ∃ a b, grid a ∧ grid b ∧ a+b=n := by
  by_cases h : n < 4
  · exact ⟨0,n,Or.inl (by decide),Or.inl h,by omega⟩
  let k := Nat.log 4 (n / 4)
  let d := 2 ^ k
  have hp : 0 < d := by dsimp [d]; positivity
  have hd : 4^k = d^2 := by
    dsimp [d]
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    rfl
  have hlo := Nat.pow_log_le_self 4 (show n / 4 ≠ 0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 4) (n / 4)
  change 4^k ≤ n/4 at hlo
  change n/4 < 4^(k+1) at hhi
  rw [pow_succ,hd] at hhi
  rw [hd] at hlo
  let r := n % d
  have hr : r < d := Nat.mod_lt _ hp
  let b := (d+r)*(d+1)
  have hb : b ≤ 3*d^2 := by
    dsimp [b]
    nlinarith [Nat.mul_le_mul_right (d+1) (show r+1 ≤ d by omega), Nat.mul_self_le_mul_self hp]
  have hb' : d^2 ≤ b := by dsimp [b]; nlinarith
  have hbdiv : d+1 ∣ b := dvd_mul_left _ _
  have hmod : b % d = r := by
    have he : b = r + (d+r+1)*d := by dsimp [b]; ring
    rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  refine ⟨n-b,b,Or.inr ⟨k,?_,?_,Or.inl ?_⟩,Or.inr ⟨k,hb',?_,Or.inr hbdiv⟩,?_⟩
  · change d^2 ≤ n-b
    omega
  · change n-b ≤ 16*d^2
    omega
  · exact Nat.modEq_iff_dvd' (by omega : b ≤ n) |>.mp hmod
  · change b ≤ 16*d^2
    omega
  · omega

lemma scale_unique {m k l : ℕ} (hk : 2^k ≤ m) (hk' : m ≤ 4*2^k)
    (hl : 2^l ≤ m) (hl' : m ≤ 4*2^l) (eq : k%3=l%3) : k=l := by
  have helper : ∀ {i j : ℕ}, 2^j ≤ m → m ≤ 4*2^i → i+3 ≤ j → False := by
    intro i j hj hi hij
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) hij
    rw [pow_add] at hpow
    have pos : 0 < 2^i := by positivity
    norm_num at hpow
    omega
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · exact helper hl hk' (by omega)
  · exact helper hk hl' (by omega)

lemma quotient_unique {m d q r : ℕ} (hd : 0<d) (hm : m ≤ 4*d)
    (hq : m^2 ≤ q*d) (hq' : q*d < (m+1)^2)
    (hr : m^2 ≤ r*d) (hr' : r*d < (m+1)^2) (eq : q%9=r%9) : q=r := by
  have helper : ∀ {i j : ℕ}, m^2 ≤ i*d → j*d < (m+1)^2 → i+9 ≤ j → False := by
    intro i j hi hj hij
    have := Nat.mul_le_mul_right d hij
    nlinarith
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · exact helper hq hr' (by omega)
  · exact helper hr hq' (by omega)

-- Within a square bin, k mod 3 determines the scale. The divisor choice
-- and the quotient mod 9 then determine the point.
lemma sparse (m : ℕ) (hm : 2 ≤ m) (S : Finset ℕ)
    (hs : ∀ n ∈ S, m^2 ≤ n ∧ n < (m+1)^2 ∧ grid n) : S.card ≤ 54 := by
  classical
  have hrepr (n : S) : ∃ (k : ℕ) (t : Fin 2) (q : ℕ),
      2^k ≤ m ∧ m ≤ 4*2^k ∧ q*(2^k+t.val)=n.val := by
    have ⟨hn,hn',hg⟩ := hs n.val n.property
    rcases hg with h | ⟨k,h1,h2,hd⟩
    · nlinarith
    · have hk : 2^k ≤ m := by
        by_contra! hh
        nlinarith [Nat.pow_le_pow_left (show m+1 ≤ 2^k by omega) 2]
      have hk' : m ≤ 4*2^k := by
        apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
        calc m^2 ≤ n.val := hn
             _ ≤ 16*(2^k)^2 := h2
             _ = (4*2^k)^2 := by ring
      rcases hd with ⟨q,hq⟩ | ⟨q,hq⟩
      · exact ⟨k,0,q,hk,hk',by simpa [Nat.mul_comm] using hq.symm⟩
      · exact ⟨k,1,q,hk,hk',by simpa [Nat.mul_comm] using hq.symm⟩
  choose k t q hk hk' he using hrepr
  let enc (n : S) : Fin 3 × Fin 2 × Fin 9 :=
    (⟨k n % 3, Nat.mod_lt _ (by decide)⟩,t n,⟨q n % 9,Nat.mod_lt _ (by decide)⟩)
  have inj : Function.Injective enc := by
    intro a b eq
    have heqk : k a % 3 = k b % 3 := congrArg (fun z : Fin 3 × Fin 2 × Fin 9 => z.1.val) eq
    have heqt : t a = t b := congrArg (fun z : Fin 3 × Fin 2 × Fin 9 => z.2.1) eq
    have heqq : q a % 9 = q b % 9 := congrArg (fun z : Fin 3 × Fin 2 × Fin 9 => z.2.2.val) eq
    have hke := scale_unique (hk a) (hk' a) (hk b) (hk' b) heqk
    have ha := he a
    rw [hke,heqt] at ha
    have hb := he b
    obtain ⟨ha1,ha2,-⟩ := hs a a.property
    obtain ⟨hb1,hb2,-⟩ := hs b b.property
    rw [←ha] at ha1 ha2
    rw [←hb] at hb1 hb2
    have eqQ := quotient_unique (by positivity) (by have := hk' b; omega) ha1 ha2 hb1 hb2 heqq
    apply Subtype.ext
    rw [←ha,←hb,eqQ]
  simpa using Fintype.card_le_of_injective enc inj

lemma bin (m : ℕ) (hm : 54 ≤ m) : ∃ e : Fin 54 ↪o ℕ,
    (∀ i, e i ∈ Finset.Ico (m^2) ((m+1)^2)) ∧
    ∀ n ∈ Finset.Ico (m^2) ((m+1)^2), grid n → n ∈ Set.range e := by
  classical
  let T := Finset.Ico (m^2) ((m+1)^2)
  let S := T.filter grid
  have hs : S.card ≤ 54 := by
    apply sparse m (by omega)
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨ht,hg⟩
    exact ⟨(Finset.mem_Ico.mp ht).1,(Finset.mem_Ico.mp ht).2,hg⟩
  have ht : 54 ≤ T.card := by
    simp only [T,Nat.card_Ico]
    have : m^2+54 ≤ (m+1)^2 := by nlinarith
    omega
  obtain ⟨U,hSU,hUT,hcard⟩ := Finset.exists_subsuperset_card_eq (Finset.filter_subset grid T) hs ht
  refine ⟨U.orderEmbOfFin hcard, fun i => hUT (U.orderEmbOfFin_mem hcard i), ?_⟩
  intro n hn hg
  rw [Finset.range_orderEmbOfFin]
  exact hSU (Finset.mem_filter.mpr ⟨hn,hg⟩)

-- Keep the initial segment and select exactly 54 entries from each later bin.
lemma sequence : ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ x, grid x → x ∈ Set.range a) ∧
    ∀ n, 2916 ≤ n → (n/54)^2 ≤ a n ∧ a n < (n/54+1)^2 := by
  classical
  choose e he he' using bin
  let a (n : ℕ) := if h : 2916 ≤ n then
    e (n/54) (by omega) ⟨n%54, Nat.mod_lt _ (by decide)⟩ else n
  have bounds (n : ℕ) (hn : 2916 ≤ n) : (n/54)^2 ≤ a n ∧ a n < (n/54+1)^2 := by
    simp only [a,dif_pos hn]
    exact Finset.mem_Ico.mp (he _ _ _)
  refine ⟨a,strictMono_nat_of_lt_succ (fun n => ?_),?_,bounds⟩
  · by_cases hn : 2916 ≤ n
    · have hs : 2916 ≤ n+1 := by omega
      by_cases hq : n/54 = (n+1)/54
      · simp only [a,dif_pos hn,dif_pos hs]
        generalize_proofs
        simp only [←hq]
        apply (e _ _).strictMono
        change n%54 < (n+1)%54
        omega
      · have hle : (n/54+1)^2 ≤ ((n+1)/54)^2 :=
          Nat.pow_le_pow_left (by omega) 2
        exact (bounds n hn).2.trans_le (hle.trans (bounds _ hs).1)
    · by_cases hs : 2916 ≤ n+1
      · have heq : n=2915 := by omega
        subst n
        simpa [a, -Nat.reduceDiv] using (show 2915 < a 2916 from
          lt_of_lt_of_le (by decide : 2915 < (2916/54)^2) (bounds 2916 (by decide)).1)
      · simp [a,hn,hs]
  · intro x hx
    by_cases h : 2916 ≤ x
    · let m := Nat.sqrt x
      have hl := Nat.sqrt_le' x
      have hu := Nat.lt_succ_sqrt' x
      change m^2 ≤ x at hl
      change x < (m+1)^2 at hu
      have hm : 54 ≤ m := by
        by_contra! hh
        have := Nat.pow_le_pow_left (show m+1 ≤ 54 by omega) 2
        omega
      obtain ⟨i,hi⟩ := he' m hm x (Finset.mem_Ico.mpr ⟨hl,hu⟩) hx
      refine ⟨m*54+i.val,?_⟩
      have ilt := i.isLt
      have large : 2916 ≤ m*54+i.val := by omega
      have div : (m*54+i.val)/54=m := by omega
      have mod : (m*54+i.val)%54=i.val := by omega
      simpa only [a,dif_pos large,div,mod] using hi
    · exact ⟨x,by simp [a,h]⟩
end Cassels

open Filter
open scoped Topology

lemma Cassels.limit {a : ℕ → ℕ} (h : ∀ n, 2916 ≤ n →
    (n/54)^2 ≤ a n ∧ a n < (n/54+1)^2) :
    Tendsto (fun n => (a n : ℝ)/(n : ℝ)^2) atTop (𝓝 ((1/54 : ℝ)^2)) := by
  let q (n : ℕ) : ℝ := (n/54 : ℕ)
  have hinv := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hconst : Tendsto (fun _ : ℕ => (1/54 : ℝ)) atTop (𝓝 (1/54)) := tendsto_const_nhds
  have hq : Tendsto (fun n : ℕ => q n / n) atTop (𝓝 (1/54)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hconst.sub hinv) hconst
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
      have hb : (n : ℝ) ≤ 54*q n+54 := by
        dsimp [q]
        exact_mod_cast (show n ≤ 54*(n/54)+54 by omega)
      field_simp
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
      have hb : 54*q n ≤ (n : ℝ) := by
        dsimp [q]
        exact_mod_cast (show 54*(n/54) ≤ n by omega)
      field_simp
      linarith
  have hq' : Tendsto (fun n : ℕ => (q n + 1) / n) atTop (𝓝 (1/54)) := by
    simpa only [add_div,add_zero] using hq.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hq.pow 2) (hq'.pow 2)
  · filter_upwards [eventually_ge_atTop 2916] with n hn
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [q]
    exact_mod_cast (h n hn).1
  · filter_upwards [eventually_ge_atTop 2916] with n hn
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [q]
    exact_mod_cast (h n hn).2.le

theorem OMA.solution : type_of% @Erdos326.erdos_326.variants.eq := by
  obtain ⟨a,hmono,hrange,hbound⟩ := Cassels.sequence
  refine ⟨a,hmono,?_,(1/54 : ℝ)^2,by norm_num,Cassels.limit hbound⟩
  apply Set.isAddBasisOfOrder_two_iff.mpr
  intro n
  obtain ⟨x,y,hx,hy,he⟩ := Cassels.cover n
  exact ⟨x,hrange x hx,y,hrange y hy,he⟩
