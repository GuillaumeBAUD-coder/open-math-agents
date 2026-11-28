import OMAReductions.R_opg_adams_conjecture_R1
import Mathlib

-- Step opg-adams-conjecture.R1.H1: Ádám's conjecture for tournaments with a vertex b of
-- in-degree (out-degree) one lying on a directed cycle. Reversing the unique in-arc (out-arc)
-- of b makes b a source (sink): every new cycle avoids b, so it uses only old arcs, while the old
-- cycle through b disappears; the cycle sets are strictly nested. Original proof.

namespace OMA.AdamDegOne

open OMA.S_opg_adams_conjecture (cycles reverse)

section
variable {n : ℕ}

lemma mem_of_mem_zip {l : List (Fin n)} {p : Fin n × Fin n} (hp : p ∈ l.zip (l.rotate 1)) :
    p.1 ∈ l ∧ p.2 ∈ l := by
  have h := List.of_mem_zip hp
  exact ⟨h.1, (List.mem_rotate).mp h.2⟩

lemma exists_pred {l : List (Fin n)} {x : Fin n} (hx : x ∈ l) :
    ∃ p ∈ l.zip (l.rotate 1), p.2 = x := by
  have hmap : (l.zip (l.rotate 1)).map Prod.snd = l.rotate 1 :=
    List.map_snd_zip (by simp)
  have : x ∈ (l.zip (l.rotate 1)).map Prod.snd := by
    rw [hmap]; exact List.mem_rotate.mpr hx
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp this
  exact ⟨p, hp, hpx⟩

lemma exists_succ {l : List (Fin n)} {x : Fin n} (hx : x ∈ l) :
    ∃ p ∈ l.zip (l.rotate 1), p.1 = x := by
  have hmap : (l.zip (l.rotate 1)).map Prod.fst = l :=
    List.map_fst_zip (by simp)
  have : x ∈ (l.zip (l.rotate 1)).map Prod.fst := by
    rw [hmap]; exact hx
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp this
  exact ⟨p, hp, hpx⟩

/-- If `b` lies on no cycle of `adj'`, every arc of `adj'` avoiding `b` is an arc of `adj`,
and `b` lies on a cycle of `adj`, then `adj'` has fewer cycles than `adj`. -/
lemma ncard_lt_of_avoid (adj adj' : Fin n → Fin n → Prop) (b : Fin n)
    (hb : ∀ l : List (Fin n), (∀ p ∈ l.zip (l.rotate 1), adj' p.1 p.2) → b ∉ l)
    (hsub : ∀ x y, adj' x y → x ≠ b → y ≠ b → adj x y)
    (hC : ∃ C ∈ cycles adj, ∃ p ∈ C, p.1 = b) :
    (cycles adj').ncard < (cycles adj).ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  obtain ⟨C0, hC0, p0, hp0, hp0b⟩ := hC
  refine ⟨?_, ?_⟩
  · rintro C ⟨l, hnd, hlen, harc, rfl⟩
    have hbl := hb l harc
    refine ⟨l, hnd, hlen, ?_, rfl⟩
    intro p hp
    have hm := mem_of_mem_zip hp
    exact hsub _ _ (harc p hp) (fun h => hbl (h ▸ hm.1)) (fun h => hbl (h ▸ hm.2))
  · intro hsub'
    obtain ⟨l, -, -, harc, rfl⟩ := hsub' hC0
    have hm := mem_of_mem_zip (List.mem_toFinset.mp hp0)
    exact hb l harc (hp0b ▸ hm.1)

/-- Ádám's conjecture for tournaments with a vertex of in-degree or out-degree one lying on a
directed cycle. -/
theorem adam_deg_one (adj : Fin n → Fin n → Prop) (hirr : ∀ i, ¬ adj i i)
    (b : Fin n) (hC : ∃ C ∈ cycles adj, ∃ p ∈ C, p.1 = b)
    (hdeg : (∃ a, ∀ x, adj x b ↔ x = a) ∨ (∃ c, ∀ y, adj b y ↔ y = c)) :
    ∃ a b, adj a b ∧ (cycles (reverse adj a b)).ncard < (cycles adj).ncard := by
  rcases hdeg with ⟨a, ha⟩ | ⟨c, hc⟩
  · have hab : adj a b := (ha a).mpr rfl
    refine ⟨a, b, hab, ncard_lt_of_avoid _ _ b ?_ ?_ hC⟩
    · intro l harc hbl
      obtain ⟨p, hp, hpb⟩ := exists_pred hbl
      have h := harc p hp
      rw [hpb] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 ⟨(ha _).mp h1, rfl⟩
      · exact hirr a (h2 ▸ hab)
    · intro x y h hx _
      rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exact absurd h1 hx
  · have hbc : adj b c := (hc c).mpr rfl
    refine ⟨b, c, hbc, ncard_lt_of_avoid _ _ b ?_ ?_ hC⟩
    · intro l harc hbl
      obtain ⟨p, hp, hpb⟩ := exists_succ hbl
      have h := harc p hp
      rw [hpb] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 ⟨rfl, (hc _).mp h1⟩
      · exact hirr b (h1 ▸ hbc)
    · intro x y h _ hy
      rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd h2 hy

end

end OMA.AdamDegOne

theorem OMA.solution : OMA.R_opg_adams_conjecture_R1.H1 := by
  intro n adj hirr _ _ hex
  obtain ⟨b, hC, hdeg⟩ := hex
  exact OMA.AdamDegOne.adam_deg_one adj hirr b hC hdeg
