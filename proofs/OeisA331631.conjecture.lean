import FormalConjectures.OEIS.«331631»
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.FieldTheory.Finite.Basic

/-! # The tripling sequence is a permutation of the positive integers

Euler's theorem makes each seed reappear as a decimal suffix. The finite history
is closed under taking predecessors along multiplication by three, so the next
block is disjoint from all earlier blocks. The least missing values increase
strictly and therefore every positive integer eventually occurs. -/

-- Credit: @zarnab222-dev

namespace A331Digits

theorem exists_stops (seed : ℕ) (_hs : 0 < seed) : ∃ e, OeisA331631.StopsAt seed e := by
  classical
  let modulus := 10 ^ (Nat.digits 10 seed).length
  have hmod : 0 < modulus := pow_pos (by decide) _
  have hsmall : seed < modulus := Nat.lt_base_pow_length_digits (by decide)
  have hcop : Nat.Coprime 3 modulus := (show Nat.Coprime 3 10 by decide).pow_right _
  let e := Nat.totient modulus
  have hrem : (seed * 3 ^ e) % modulus = seed := by
    have hc := (Nat.ModEq.pow_totient hcop).mul_left seed
    change (seed * 3 ^ e) % modulus = (seed * 1) % modulus at hc
    simpa only [mul_one, Nat.mod_eq_of_lt hsmall] using hc
  have hfound : ∃ j, 0 < j ∧ OeisA331631.ContainsSeed seed (seed * 3 ^ j) := by
    refine ⟨e, Nat.totient_pos.mpr hmod, ?_⟩
    let q := seed * 3 ^ e / modulus
    have hv : seed + modulus * q = seed * 3 ^ e := by
      simpa only [hrem] using Nat.mod_add_div (seed * 3 ^ e) modulus
    have hd := Nat.digits_append_digits (b := 10) (m := q) (n := seed) (by decide)
    change Nat.digits 10 seed ++ Nat.digits 10 q = Nat.digits 10 (seed + modulus * q) at hd
    rw [hv] at hd
    exact ⟨[], Nat.digits 10 q, by simpa using hd⟩
  refine ⟨Nat.find hfound, (Nat.find_spec hfound).1, (Nat.find_spec hfound).2, ?_⟩
  intro j hj hlt hjc
  exact (Nat.find_min hfound hlt) ⟨hj, hjc⟩


end A331Digits

namespace A331
open OeisA331631

theorem extend_good (h : List ℕ) (s k : ℕ) (hs : LeastMissing h s) (hdup : h.Nodup)
    (hpred : ∀ x : ℕ, x * 3 ∈ h → x ∈ h) :
    (h ++ blockValues s k).Nodup ∧
      (∀ x : ℕ, x * 3 ∈ h ++ blockValues s k → x ∈ h ++ blockValues s k) := by
  obtain ⟨hspos, hsabs, hleast⟩ := hs
  have hfresh (j : ℕ) : s * 3^j ∉ h := by
    induction j with
    | zero => simpa using hsabs
    | succ j ih =>
      intro hmem
      exact ih (hpred _ (by simpa [pow_succ, Nat.mul_assoc] using hmem))
  have hinj : Function.Injective (fun j : ℕ => s * 3^j) := by
    intro i j hij
    exact (pow_right_strictMono₀ (by decide : 1 < (3:ℕ))).injective
      (Nat.eq_of_mul_eq_mul_left hspos hij)
  constructor
  · apply List.nodup_append'.2
    refine ⟨hdup, List.Nodup.map hinj List.nodup_range, ?_⟩
    intro x hx hx'
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx'
    exact hfresh j hx
  · intro x hx
    rcases List.mem_append.mp hx with hold | hnew
    · exact List.mem_append_left _ (hpred _ hold)
    · obtain ⟨j, hj, heq⟩ := List.mem_map.mp hnew
      cases j with
      | zero =>
        have hsx : s = x * 3 := by simpa using heq
        exact List.mem_append_left _ (hleast x (Finset.mem_Ico.mpr ⟨by omega, by omega⟩))
      | succ j =>
        have hval : s * 3^j = x := by
          apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 3)
          simpa [pow_succ, Nat.mul_assoc] using heq
        exact List.mem_append_right _ (List.mem_map.mpr
          ⟨j, List.mem_range.mpr (by have := List.mem_range.mp hj; omega), hval⟩)

end A331

namespace A331

open OeisA331631

private theorem exists_seed (hist : List ℕ) : ∃ s, LeastMissing hist s := by
  classical
  have bound : ∃ s : ℕ, 0 < s ∧ s ∉ hist := by
    let M := hist.toFinset.sup id
    refine ⟨M+1, by omega, ?_⟩
    intro hm
    have hle : M + 1 ≤ M := Finset.le_sup (f := id) (List.mem_toFinset.mpr hm)
    omega
  refine ⟨Nat.find bound, (Nat.find_spec bound).1, (Nat.find_spec bound).2, ?_⟩
  intro v hv
  have hr := Finset.mem_Ico.mp hv
  by_contra hmiss
  have hle := Nat.find_min' bound (m := v) (And.intro (by omega) hmiss)
  omega

theorem histories
    (termination : ∀ s : ℕ, 0 < s → ∃ k, StopsAt s k)
    (extension : ∀ (l : List ℕ) (s k : ℕ), LeastMissing l s → l.Nodup →
      (∀ x : ℕ, x*3 ∈ l → x ∈ l) →
      (l ++ blockValues s k).Nodup ∧ (∀ x : ℕ, x*3 ∈ l ++ blockValues s k →
        x ∈ l ++ blockValues s k)) :
    ∃ (h : ℕ → List ℕ) (s k : ℕ → ℕ), h 0 = [] ∧
      (∀ i, h (i+1) = h i ++ blockValues (s i) (k i)) ∧
      (∀ i, LeastMissing (h i) (s i)) ∧ (∀ i, StopsAt (s i) (k i)) ∧
      ∀ i, (h i).Nodup := by
  classical
  choose seed hseed using exists_seed
  choose stop hstop using fun l => termination (seed l) (hseed l).1
  let h : ℕ → List ℕ := Nat.rec [] fun _ l => l ++ blockValues (seed l) (stop l)
  have good (i : ℕ) : (h i).Nodup ∧ ∀ x : ℕ, x*3 ∈ h i → x ∈ h i := by
    induction i with
    | zero => simp [h]
    | succ n ih => exact extension (h n) _ _ (hseed _) ih.1 ih.2
  exact ⟨h,fun i => seed (h i),fun i => stop (h i),rfl,fun _ => rfl,
    fun i => hseed _,fun i => hstop _,fun i => (good i).1⟩

end A331

open OeisA331631

namespace A331

theorem assemble (h : ℕ → List ℕ) (s k : ℕ → ℕ) (h0 : h 0 = [])
    (hstep : ∀ i, h (i+1) = h i ++ blockValues (s i) (k i))
    (hmiss : ∀ i, LeastMissing (h i) (s i)) (hstop : ∀ i, StopsAt (s i) (k i))
    (hnodup : ∀ i, (h i).Nodup) : type_of% @OeisA331631.conjecture := by
  have length_step (i : ℕ) : (h (i+1)).length = (h i).length + k i + 1 := by
    rw [hstep, List.length_append, block_values_length, Nat.add_assoc]
  have enough (i : ℕ) : i ≤ (h i).length := by
    induction i with
    | zero => omega
    | succ i ih => rw [length_step]; omega
  have histPrefix {i j : ℕ} (hij : i ≤ j) : List.IsPrefix (h i) (h j) := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hij
    clear hij
    induction d with
    | zero => exact List.prefix_refl _
    | succ d ih =>
      rw [← Nat.add_assoc, hstep]
      exact ih.trans (List.prefix_append _ _)
  let a (n : ℕ) := (h (n+1))[n]!
  have agree (i n : ℕ) (hn : n < (h i).length) : a n = (h i)[n] := by
    have hn' : n < (h (n+1)).length := by have := enough (n+1); omega
    change (h (n+1))[n]! = _
    rw [getElem!_pos (h (n+1)) n hn']
    rcases le_total (n+1) i with hi | hi
    · exact (histPrefix hi).getElem hn'
    · exact ((histPrefix hi).getElem hn).symm
  have occurs (i v : ℕ) : v ∈ h i ↔ ∃ n < (h i).length, a n = v := by
    rw [List.mem_iff_getElem]
    exact exists_congr fun n => ⟨fun ⟨hn,e⟩ => ⟨hn,(agree i n hn).trans e⟩,
      fun ⟨hn,e⟩ => ⟨hn,(agree i n hn).symm.trans e⟩⟩
  have at_block (i j : ℕ) (hj : j ≤ k i) :
      a ((h i).length + j) = s i * 3 ^ j := by
    have hn : (h i).length + j < (h (i+1)).length := by rw [length_step]; omega
    rw [agree (i+1) _ hn]
    simp [hstep i, List.getElem_append_right, blockValues]
  have start (i : ℕ) : a (h i).length = s i := by simpa using at_block i 0 (Nat.zero_le _)
  have seen (i : ℕ) : s i ∈ h (i+1) := by
    exact (occurs _ _).mpr ⟨(h i).length, by rw [length_step]; omega, start i⟩
  have seed_increases (i : ℕ) : s i < s (i+1) := by
    by_contra! he
    have hh := hmiss (i+1)
    apply hh.2.1
    obtain hlt | heq := lt_or_eq_of_le he
    · rw [hstep]
      exact List.mem_append_left _ ((hmiss i).2.2 _ (Finset.mem_Ico.mpr ⟨hh.1,hlt⟩))
    · rw [heq]
      exact seen i
  refine ⟨a, ⟨fun i => (h i).length,k, by simp [h0], fun i => ?_⟩, ?_, ?_⟩
  · dsimp only
    rw [start]
    refine ⟨⟨⟨(hmiss i).1, ?_⟩,?_⟩,hstop i,at_block i,length_step i⟩
    · intro n hn he
      exact (hmiss i).2.1 ((occurs _ _).mpr ⟨n,hn,he⟩)
    · intro v hv
      by_contra! hlt
      obtain ⟨n,hn,he⟩ := (occurs i v).mp ((hmiss i).2.2 _ (Finset.mem_Ico.mpr ⟨hv.1,hlt⟩))
      exact hv.2 _ hn he
  · intro n m he
    let i := n + m + 1
    have hL := enough i
    have hn : n < (h i).length := by dsimp [i] at hL ⊢; omega
    have hm : m < (h i).length := by dsimp [i] at hL ⊢; omega
    exact (hnodup i).getElem_inj_iff.mp ((agree i n hn).symm.trans (he.trans (agree i m hm)))
  · intro v hv
    have major (i : ℕ) : i < s i := by
      induction i with
      | zero => exact (hmiss 0).1
      | succ i ih => have := seed_increases i; omega
    obtain ⟨n,_,he⟩ := (occurs v v).mp ((hmiss v).2.2 v (Finset.mem_Ico.mpr ⟨hv,major v⟩))
    exact ⟨n,he⟩

end A331

theorem OMA.solution : type_of% @OeisA331631.conjecture := by
  obtain ⟨h, s, k, h0, hstep, hmiss, hstop, hn⟩ :=
    A331.histories A331Digits.exists_stops A331.extend_good
  exact A331.assemble h s k h0 hstep hmiss hstop hn
