import OMAStatements.S_oeis_a029858
import Mathlib

namespace A029858

def G (k : ℕ) : Finset ℕ := (Finset.range (10 ^ k)).filter
  (fun m => m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ Finset.range 7)

lemma mem_G (k m : ℕ) :
    m ∈ G k ↔ m < 10 ^ k ∧ m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ Finset.range 7 := by
  unfold G
  rw [Finset.mem_filter, Finset.mem_range]

lemma digits_step (q r : ℕ) (hr : r < 10) (h : 10 * q + r ≠ 0) :
    Nat.digits 10 (10 * q + r) = r :: Nat.digits 10 q := by
  have h1 : (10 * q + r) % 10 = r := by omega
  have h2 : (10 * q + r) / 10 = q := by omega
  rw [Nat.digits_def' (by norm_num) (by omega), h1, h2]

lemma G_succ (k : ℕ) : G (k + 1) =
    ((insert 0 (G k)) ×ˢ ({7, 8, 9} : Finset ℕ)).image (fun x : ℕ × ℕ => 10 * x.1 + x.2) := by
  have hpow : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
  have hpos : 0 < 10 ^ k := by positivity
  ext m
  rw [mem_G, Finset.mem_image]
  constructor
  · rintro ⟨hlt, hne, hd⟩
    have hm : 10 * (m / 10) + m % 10 = m := by omega
    refine ⟨(m / 10, m % 10), ?_, hm⟩
    have hdig := digits_step (m / 10) (m % 10) (by omega) (by omega)
    rw [hm] at hdig
    rw [hdig] at hd
    rw [Finset.mem_product]
    constructor
    · show m / 10 ∈ insert 0 (G k)
      rw [Finset.mem_insert, mem_G]
      by_cases h0 : m / 10 = 0
      · left
        exact h0
      · right
        exact ⟨by omega, h0, fun d hdm => hd d (List.mem_cons_of_mem _ hdm)⟩
    · show m % 10 ∈ ({7, 8, 9} : Finset ℕ)
      have h7 := hd (m % 10) List.mem_cons_self
      rw [Finset.mem_range] at h7
      have h10 : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  · rintro ⟨⟨q, r⟩, hx, rfl⟩
    rw [Finset.mem_product] at hx
    obtain ⟨hq, hr⟩ := hx
    have hr' : r = 7 ∨ r = 8 ∨ r = 9 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hr
    have hq' : q = 0 ∨ q ∈ G k := by
      simpa only [Finset.mem_insert] using hq
    have hqk : q < 10 ^ k ∧ ∀ d ∈ Nat.digits 10 q, d ∉ Finset.range 7 := by
      rcases hq' with h0 | hG
      · subst h0
        refine ⟨hpos, ?_⟩
        intro d hd
        simp at hd
      · rw [mem_G] at hG
        exact ⟨hG.1, hG.2.2⟩
    show 10 * q + r < 10 ^ (k + 1) ∧ 10 * q + r ≠ 0 ∧
      ∀ d ∈ Nat.digits 10 (10 * q + r), d ∉ Finset.range 7
    refine ⟨by omega, by omega, ?_⟩
    rw [digits_step q r (by omega) (by omega)]
    intro d hd
    rcases List.mem_cons.1 hd with h | h
    · rw [Finset.mem_range]
      omega
    · exact hqk.2 d h

lemma card_G_succ (k : ℕ) : (G (k + 1)).card = ((G k).card + 1) * 3 := by
  have h0 : 0 ∉ G k := fun h => ((mem_G k 0).1 h).2.1 rfl
  have hinj : Set.InjOn (fun x : ℕ × ℕ => 10 * x.1 + x.2)
      (((insert 0 (G k)) ×ˢ ({7, 8, 9} : Finset ℕ) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product] at hx hy
    have hx2 : x.2 = 7 ∨ x.2 = 8 ∨ x.2 = 9 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx.2
    have hy2 : y.2 = 7 ∨ y.2 = 8 ∨ y.2 = 9 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hy.2
    have hxy' : 10 * x.1 + x.2 = 10 * y.1 + y.2 := hxy
    apply Prod.ext <;> omega
  have h3 : ({7, 8, 9} : Finset ℕ).card = 3 := by decide
  rw [G_succ, Finset.card_image_of_injOn hinj, Finset.card_product,
    Finset.card_insert_of_notMem h0, h3]

lemma card_G (k : ℕ) : 2 * (G k).card + 3 = 3 ^ (k + 1) := by
  induction k with
  | zero =>
    have hempty : G 0 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro m hm
      obtain ⟨h1, h2, _⟩ := (mem_G 0 m).1 hm
      rw [pow_zero] at h1
      omega
    rw [hempty]
    norm_num
  | succ j ih =>
    rw [card_G_succ]
    have e : 3 ^ (j + 1 + 1) = 3 * 3 ^ (j + 1) := by ring
    omega

end A029858

theorem OMA.solution : type_of% @OMA.S_oeis_a029858.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := A029858.card_G k
  unfold OMA.S_oeis_a029858.a
  rw [Nat.add_sub_cancel]
  change (A029858.G k).card = (3 ^ (k + 1) - 3) / 2
  omega
