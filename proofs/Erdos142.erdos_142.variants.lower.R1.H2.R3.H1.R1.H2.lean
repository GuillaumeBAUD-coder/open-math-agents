import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1

/-! 公差の代表元が法の半分以下になる向きに等差数列を読む。各項は区間内にあるので、次の項まで足しても法に達しない。 -/

namespace OMA.PrimeInterval

-- 極値集合の構成はErdős問題142の分解R3(PR #7180)に従う。
lemma extremizer {k N : ℕ} (hk : 1 < k) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ Erdos142.r k N = S.card ∧
      ¬ ∃ b t : ℕ, 0 < t ∧ ∀ i < k, b + i * t ∈ S := by
  let C := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hk' : (1 : ℕ∞) < k := by exact_mod_cast hk
  have hnon : C.Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
    simp [Set.IsAPOfLengthFree, Set.not_isAPOfLength_empty (zero_lt_one.trans hk')]
  have hbound : BddAbove C := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, _, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, hcard⟩ := Nat.sSup_mem hnon hbound
  refine ⟨S, hS, hcard.symm, ?_⟩
  rintro ⟨b, t, ht, terms⟩
  let f (i : ℕ) := b + i * t
  have hinj : f.Injective := (add_right_injective b).comp (mul_left_injective₀ ht.ne')
  apply hk'.not_ge (hf (f '' {i | i < k}) (Set.image_subset_iff.mpr terms) ⟨b, t, ?_, ?_⟩)
  · rw [ENat.card_coe_set_eq, hinj.encard_image, Set.Nat.encard_range]
  · ext
    simp [f, Set.image]

lemma no_wrap_progression {p N k : ℕ} [NeZero p] {S : Finset ℕ}
    (hp : 2 * N < p) (hS : ∀ n ∈ S, n ≤ N)
    (hfree : ¬ ∃ b t : ℕ, 0 < t ∧ ∀ i < k, b + i * t ∈ S)
    (a d : ZMod p) (hm : ∀ i < k, (a + (i : ZMod p) * d).val ∈ S) : d = 0 := by
  by_contra hd
  have forward (b e : ZMod p) (hne : e ≠ 0) (hs : 2 * e.val ≤ p)
      (hb : ∀ i < k, (b + (i : ZMod p) * e).val ∈ S) : False := by
    apply hfree
    refine ⟨b.val, e.val, ZMod.val_pos.mpr hne, ?_⟩
    have line (i : ℕ) (hi : i < k) : (b + (i : ZMod p) * e).val = b.val + i * e.val := by
      induction i with
      | zero => simp
      | succ i ih =>
        have hj : i < k := by omega
        have hbnd := hS _ (hb i hj)
        rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, ZMod.val_add_of_lt (by omega),
          ih hj, Nat.succ_mul, Nat.add_assoc]
    exact fun i hi ↦ line i hi ▸ hb i hi
  by_cases hs : 2 * d.val ≤ p
  · exact forward a d hd hs hm
  · let : NeZero d := ⟨hd⟩
    apply forward (a + ((k - 1 : ℕ) : ZMod p) * d) (-d) (neg_ne_zero.mpr hd)
    · rw [ZMod.val_neg_of_ne_zero]
      omega
    · intro i hi
      have h := hm (k - 1 - i) (by omega)
      rw [Nat.cast_sub (by omega : i ≤ k - 1)] at h
      convert h using 2
      ring

end OMA.PrimeInterval

open OMA.PrimeInterval

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  classical
  intro k N hk hN
  obtain ⟨S, hS, hcard, hfree⟩ := extremizer (N := N) (k := k) (by omega)
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  let : NeZero p := ⟨hp.ne_zero⟩
  have bound {n : ℕ} (hn : n ∈ S) : n ≤ N := (Finset.mem_Icc.mp (hS hn)).2
  have small {n : ℕ} (hn : n ∈ S) : n < p := (bound hn).trans_lt (by omega)
  refine ⟨p, hp, S.image (Nat.cast : ℕ → ZMod p), hlo, by omega, hcard.trans ?_, ?_⟩
  · exact (Finset.card_image_of_injOn ((CharP.natCast_injOn_Iio (ZMod p) p).mono
      (fun _ hn ↦ small hn))).symm
  · intro a d hA
    apply no_wrap_progression hlo (fun _ hn ↦ bound hn) hfree a d
    intro i hi
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (hA ⟨i, hi⟩)
    change (n : ZMod p) = a + (i : ZMod p) * d at he
    simpa only [← he, ZMod.val_natCast_of_lt (small hn)] using hn
