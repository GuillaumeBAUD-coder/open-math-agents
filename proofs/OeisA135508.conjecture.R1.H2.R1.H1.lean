import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1

/-!
For every eligible prime q, try the 47 multipliers in its residue class modulo
six. For large candidates r, coprimality with the common multiple of all integers
through 16000 certifies primality up to 16000 squared. A preliminary gcd with
the product of the primes up to 47 cheaply rejects most composites. The kernel
checks disjoint intervals one at a time to bound peak memory use.
-/

namespace OMA.DivisorWitness

/-- The least common multiple of the integers from 1 to 16000. -/
private def multiple : ℕ := 0x23a8fb4a313100c165776678bb64682df8922d0758e06c0b5b5e2630494b5b0f3c15bd01155527cb59d856eef94005c73dd18f51b640fc0331220a22fc00886cfe34e9b7e48d2bf87fed56a93bff7343a06269eba57998f20824ea926fe6caf038319fc7a94d8c8204646b149d9dbe1db06dfdbd5d7d322fe33a03158c6a99a34256d37b2788cfe3d76e9c81b1e21c59c377f0d35985c6c6a4a3eea128b0ce30bd26bece7d03bd7d7f543b2997e218d76371a6357416996a1a29923d3466e8283a7feec997c36c6fc871f3a46317cb227f1a1450dee55aae070b7c2d3d65982289f519365ca253f0848223bc17fd0ddacb4c3d2c4af92e5a5b7c5dd7124f485339e6f03f75cf9d5f51a75078d59396c745c026fa80ad26fa3dd1c40b2aba206deaf20df8aa72899f0c7fd8a6160ad263a0d86a0ff5120fee5a6f502c455814c8229f03207e5a8db619d234e8823d5ec1860d7fa3a9b2b4256673a459b44e8f70a6e467c7fde74313dff52dc925a30d791b841de7638c5f18ffc799d446b85e366059b4fa832aa16515f0feaf2a5f01830cc737781f0b7ba257c9dc29a5955b1c7de7dfa3aa21aaa9d5bdc5fd601bc83b998072bc44b7a7b9d58bec27f9f9280f8bb6ea10532021d53901b732d537327aded0a58aeaacd95b21965955f71f3d73f2d52b8dd4534ecff71294d99603df1d3dad190048074e9c782ec107f2ba10ad64048a4436479aadea06a14bf749da595a3974889e4b127adaca20b4a863de89908ce5c5d54b83181eef3005100613552505fff67a7de0a8f28b91d5ae0517b14710307581bb787084677fe2e30747e90a6071863c49befb422e7c397e1b597dde892026b4861588b9f0d47079b77fd95ead69cd48382fdc57966b72cd5f296510b5355a82c18c1cfa809108b2579c2eb843dfce90222dbc7ab90f562f60c2ee8c1425e92b047f56bc054ba8128dd6410219be8a1840a12f1c851adf86648fc4ca52d57cfd83d0c64d80b847cee292a6ac253f2d9d329272f5b7db19ddd5750012eafead3b25672d449fcbaf3a367a9079e7d3f118d5078eda8851a87068b6e3a372d94b7fa1e608e95cdf7bc5fe75c85d90e6e896ad571f1b208a26c41036916538ba4cab42b1e5c419353b9e7de842f1b052b1c2efa92deaf80fa9f1310fe94f398c66d33b80e81652e789e9643ed8ff182cb78ba432c7901dd1bd3cbb8ded8a85abee5240ac08d9824bdf63be070296ab7b5498d67629055104061ddb1becb0b6b812f09e0fd629e20ff4546874297f5877e11357cb01d37b4e6c92c5108dbd37bc0e8a389332ab80a5c287bdb3e5bd4fa7a03710fd9ce1d400f0eb1bb14f6c89c61a936238ef4483a89ab7a4c23d6eeda738eaf9ea5b6f5ca1acbaa4893ff70db26109e4202c31766759e407cc3eded07609121570ca122e66f79633f4a970146c6eb7a3185a3c813a5bb02cb801f69658f8a534c961a9d17fe71a9c983709954fcb5b74f4579db56353c87d4abf441070ebc56aaf44dc395c0f383986cd0401714eeee20c9c52181c639416662e311e778202b776f8d7182024fe37cc1962cc66d625e0a0242d0416bc35264dc9167fe266dd8025345ccf0d96d7580857872bc8fdee74d1c6331d1d094d3eba91b7d864b88b9dfc1e98dd5194baaba68cacbd45806d9ad3a46fcb3026541a83294eac6dc541740b488d672307d8f5ce0900dae14455928ff795d2796b75f5ac2860e1f36ff66d6fe14e89e60fe5f37c80b24e72b75c59b12fc7cbe040891759ae8fb7c61edd3ea9fb8e01cbd3f4c1c3f1689838cf9648089b0c3b612ffc4d079ad9066c56ae567feb944e43e7bad7aeda72af86215cea52978beb1100c72ed7d19c6a744794c3ff9fca5b1193200d2811dea2b4dfec3e4f859ed3b2de208a18c4876dc5935df3c1777aab61a759d00ed1495de5cd645b2bfb4a8e34efd2a0a5bdcae16b834688572ad3f0f8c57a1d8f4d8b5fbf814e1db93e0545f12510f015336202d8982fe54ca36a0a81b3292becc8241f8b0065f786f34a3a0abf9e2f36671b96242852579128bc62025b3f4df0dc6e1216ce1ffed5ab8499579f5773efa8aaa46e38d99748948b6a617f6a102c6d9c239eafbc27ef4b7ff4bfc2057349193aaa2f77e61eef0df7cb485bb3b61544a1ca58a2d3f911233aae1c3d113c9a489e69c04f8feb8bfa4dcf7a6353cdafaa76b00d7d284a1412f138b05d55bb1f11bf63b9029ed36d2e9da57f56f181272bd0835ee9d62b9ebac568686ebe4674e45023859984f2ecc75acf5649f7d03099948fb467c031c9577168b62fc92ac38d1e0d0b7ddf64479d2f693c4294a67472c2482e2eb8e629ca30d564cf52145ac897c38d91c675ff21198e039be8f868fb8355e7c754e68b695a45232242b4ea128fe5a3ac1923da808c25a07b0ac4f581bbc6f73b7e169a3695a882bb002063a0379e00d0150d3c78fc54808ff5fe98a321d8a1da26caf98dd522645c85e0bceab8380efb9ceef6b27dec9ebca7851745898fdc138b905357165d2cea292f1b1320566ca5f619a147973f50c161868aaa58036029c9f234fd4e953296d006bc16ded44738b673e334aec6f65ede795b4e6a04b382f4f6d22ab1e0f180f0840f84fa9efaa6fc79e3980217470ab02b29747ccd6ccf1db52d00af5c0ce27f5ebde006115fc951b783ad612ce23207201a53379e8716ff89eca64603bf9e1ebea5ec8c4f15880841c08b21dfd0fe3110daff51070838c3356d4930799c8dfb61387c05f08daa28bd817d043b98d8767c69cfc77c4b6b076d7524cebf00f42307424169f638a00075e59ea9c40c0d5eb6aedc24edeb630b62104e7af7cc77821713fa7c9ab8bf371d190005f4d5be09c98d434335e5f1c5fbb468943104c9158374e913dec53488f64c8b9be63fad8d97d11c69bd26bdd10bc0c96983c60349c8808130d25630df78c3b2c61608c1d7777235891e64650545d375f04347974c11f8f70e5771e9a36ac81423f7135e39343f171a42909e5520b0471a6d10cfe7d50f9e13d1457313991218a3e27151a6eafe3b7d45602166aa07b4870bd3c3fb08245cd9bff6aaceae2c74495c41acc3fb304f15e3b0466ad33f11540dce0b3e7405398b09a2e7e2c3a7e4d1c5e5e9eb1fa95b95bf2f4763c60c26147fff06ef08623908cb9e64ea92a4321f2938d5f6e5786113518e9dd54dcb99ab6e76a362603c828567fa41311216ede58c5db86295f81098322ac8ea80970fbf0d218723a9ac7e14b0211b15697859285428b4bf7d870309250d94686461fa566cc7d1fad7bac908e42d5efac0fb990d058ae0e4df61bab58a8f0b25a7f7c67087d5d9634bd8a3605cb74dfa45d22494102a67f5016d36ce3163e7538bcc96a5ff714ce276f499aab4e5fb11aa890e32b60c1d3bd50a0494a2ad06d7149ae25f73fd5e9cfca1fcecaf87cfb0768b579fa7dc344dea77a863c3e2c800523ff51a0de7db798785f4719cf35765c49e6419ef9288df5f0676ab187c458d9ed2b4917bf8036cfe2f6372b649a51b9321be72db5a8a67f099599185da9eb5c182f5766df0627b8ec465464922ebcb8be81e488c2bff564237e577817267baa9d33f14a310fd96e9d73876a9624d2bba4ef7f15bbbcd34afbdf8a8878564cb0b1f53ca2677e991c810a63d95ad64f47d74428752d8f945cc872799edad8a5c0663aec5d0283e0f415e645270e779a29b22814621d02791feaba0e482b5d21f4b22ab39b293660e7d1a7a2fc3fe26d04225e3c22565159dc1049c7cdb5a4d12ffcfb9540754029568d619039afc0acd679671df779f2c8b356a254d277b01806a6b5d56347f85bbfe2cd5c43dbc0171d127610167a905d711f57566ca559b99e67ac6b7faf18a7d773de44ba1c1579179f51f98cac7191a95a14d127b2f10641b78ce92b88e87f6b5e57e8d5bcf13cde1fdb892272aff561dba9aba5673e6eaeb890289cfb433ac05ee506cebc17a903b7c341bf85ea41ac43e18df2ef485196f59192849c3899157488a0a622ed5f7218f1bf9e687bad9d279a84022c323db4abcfbe49da000

/-- The least common multiple of the integers from 1 to 1000. -/
private def smallMultiple : ℕ := 0x3bfd01c99d32f9bf2d7478a137ab39c4e570e9600c1a386143cf5bee514292077e2ca340a92232423c5b7b0e2427b3516a021b0ab4a017e1e72506c07f1cff615d0c48c8de5c25f386cbe1e2813d21eafe9f512ebb987a0b6b33bcfb7c0eb473afd46cebed88592f41b76b8621cacb3f191e5f4c38a974fb911d791d690befc93f8efa7bfbffe5f01a2df53aedb7c4e15e8ae3dcd429d22eb375917a5fe24244405b0a514d0da596270aa98ec86085e894c17a00

/-- A Boolean test on a half-open range, computed from its upper end. -/
private def allFrom (f : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => f (lo+n) && allFrom f lo n

private def Holds (f : ℕ → Bool) (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → n < hi → f n = true

private lemma holdsFrom {f : ℕ → Bool} {lo k : ℕ} (h : allFrom f lo k = true) :
    Holds f lo (lo+k) := by
  induction k with
  | zero =>
    intro n hl hh
    omega
  | succ k ih =>
    rw [allFrom, Bool.and_eq_true] at h
    intro n hl hh
    by_cases hk : n = lo+k
    · simpa [hk] using h.1
    · exact ih h.2 n hl (by omega)

private lemma join {f : ℕ → Bool} {lo mid hi : ℕ}
    (a : Holds f lo mid) (b : Holds f mid hi) : Holds f lo hi := by
  intro n hl hh
  by_cases hm : n < mid
  · exact a n hl hm
  · exact b n (by omega) hh

/-- Check consecutive blocks while keeping each recursion shallow. -/
private def blocks (f : ℕ → Bool) (lo width count : ℕ) : Bool :=
  allFrom (fun i => allFrom f (lo+i*width) width) 0 count

private lemma holdsBlocks {f : ℕ → Bool} {lo width count : ℕ}
    (h : blocks f lo width count = true) : Holds f lo (lo+count*width) := by
  induction count with
  | zero =>
    intro n hl hh
    omega
  | succ k ih =>
    change (allFrom f (lo+(0+k)*width) width && blocks f lo width k) = true at h
    rw [Bool.and_eq_true, Nat.zero_add] at h
    have last := holdsFrom h.1
    rw [Nat.succ_mul, ← Nat.add_assoc]
    exact join (ih h.2) last

private def dividesMultiple (n : ℕ) : Bool := decide (n ∣ multiple)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 5000 in
private lemma cover : Holds dividesMultiple 2 16001 := by
  apply join (mid := 8002)
  · apply join (mid := 4002)
    · exact holdsBlocks (lo := 2) (width := 100) (count := 40) (by decide +kernel)
    · exact holdsBlocks (lo := 4002) (width := 100) (count := 40) (by decide +kernel)
  · apply join (mid := 12002)
    · exact holdsBlocks (lo := 8002) (width := 100) (count := 40) (by decide +kernel)
    · apply join (mid := 15902)
      · exact holdsBlocks (lo := 12002) (width := 100) (count := 39) (by decide +kernel)
      · exact holdsFrom (lo := 15902) (k := 99) (by decide +kernel)

/-- The least common multiple through 127 handles small candidates. -/
private def mediumMultiple : ℕ := 0x45b5b958f486887e2d3e2fd27f8830e26b0eb0a3c593c0

private lemma medium_cover : Holds (fun n => decide (n ∣ mediumMultiple)) 2 128 :=
  holdsFrom (lo := 2) (k := 126) (by decide +kernel)

private lemma prime_of_sieve {n b M : ℕ} (hn : 1 < n) (hs : n ≤ b^2)
    (hg : n.gcd M = 1) (hcover : Holds (fun d => decide (d ∣ M)) 2 (b+1)) :
    n.Prime := by
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
  have hsmall : n.minFac ≤ b := by
    by_contra! hyp
    have : b^2 < n.minFac^2 := Nat.pow_lt_pow_left hyp (by decide)
    omega
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hd := hcover n.minFac hp.two_le (by omega)
  have hgcd := Nat.dvd_gcd (Nat.minFac_dvd n) (of_decide_eq_true hd)
  rw [hg] at hgcd
  exact hp.not_dvd_one hgcd

private def certifiedPrime (n : ℕ) : Bool :=
  if n ≤ 127 then decide n.Prime
  else if n ≤ 127^2 then decide (n.gcd mediumMultiple = 1)
  else decide (n.gcd 614889782588491410 = 1) &&
    decide (n ≤ 16000^2 ∧ n.gcd multiple = 1)

private lemma certifiedPrime_sound {n : ℕ} (h : certifiedPrime n = true) : n.Prime := by
  unfold certifiedPrime at h
  split at h
  · exact of_decide_eq_true h
  · split at h
    · exact prime_of_sieve (by omega) (by assumption) (of_decide_eq_true h) medium_cover
    · obtain ⟨hbound, hgcd⟩ := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
      exact prime_of_sieve (by omega) hbound hgcd cover

private def test (q k : ℕ) : Bool :=
  let r := q*k-2
  certifiedPrime r && decide (5 < r ∧ r < q^2 ∧ r%3 = 2 ∧ q ∣ r+2)

private def Witness (q : ℕ) : Prop :=
  ∃ r : ℕ, r.Prime ∧ 5 < r ∧ r < q^2 ∧ r%3 = 2 ∧ q ∣ r+2

private lemma test_sound {q k : ℕ} (h : test q k = true) : Witness q := by
  have ht := Bool.and_eq_true_iff.mp h
  exact ⟨q*k-2, certifiedPrime_sound ht.1, of_decide_eq_true ht.2⟩

/-- Try the multipliers in the appropriate residue class modulo six. -/
private def search (q k : ℕ) : ℕ → Bool
  | 0 => false
  | m+1 => test q k || search q (k+6) m

private lemma search_sound {q k m : ℕ} (h : search q k m = true) : Witness q := by
  induction m generalizing k with
  | zero => contradiction
  | succ m ih =>
    rcases Bool.or_eq_true_iff.mp h with hk | hk
    · exact test_sound hk
    · exact ih hk

private def skip (q : ℕ) : Bool :=
  if q ≤ 47 then !decide q.Prime
  else if q ≤ 1000 then decide (q.gcd 614889782588491410 ≠ 1)
  else decide (q.gcd 614889782588491410 ≠ 1) || decide (q.gcd smallMultiple ≠ 1)

set_option maxRecDepth 4000 in
private lemma multiple_dvd_factorial : smallMultiple ∣ Nat.factorial 1000 := by decide +kernel

private lemma wheel_dvd_factorial : 614889782588491410 ∣ Nat.factorial 47 := by decide +kernel

private lemma skip_prime {q : ℕ} (hq : q.Prime) : skip q = false := by
  have cop {s b : ℕ} (hl : ¬ q ≤ b) (hs : s ∣ b.factorial) : q.gcd s = 1 :=
    (hq.coprime_iff_not_dvd.mpr (fun h => hl (hq.dvd_factorial.mp (h.trans hs)))).gcd_eq_one
  unfold skip
  split
  · simp [hq]
  · rename_i hlarge
    split
    · simp [cop hlarge wheel_dvd_factorial]
    · rename_i hbig
      simp [cop hlarge wheel_dvd_factorial, cop hbig multiple_dvd_factorial]

private def check (q : ℕ) : Bool :=
  skip q || search q (if q%3=1 then 1 else 5) 47

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 5000 in
private lemma checked : Holds check 5 1000001 := by
  apply join (mid := 500005)
  · apply join (mid := 250005)
    · apply join (mid := 125005)
      · apply join (mid := 60005)
        · apply join (mid := 30005)
          · apply join (mid := 15005)
            · apply join (mid := 5005)
              · exact holdsBlocks (lo := 5) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 10005)
                · exact holdsBlocks (lo := 5005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 10005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 20005)
              · exact holdsBlocks (lo := 15005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 25005)
                · exact holdsBlocks (lo := 20005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 25005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 45005)
            · apply join (mid := 35005)
              · exact holdsBlocks (lo := 30005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 40005)
                · exact holdsBlocks (lo := 35005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 40005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 50005)
              · exact holdsBlocks (lo := 45005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 55005)
                · exact holdsBlocks (lo := 50005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 55005) (width := 100) (count := 50) (by decide +kernel)
        · apply join (mid := 90005)
          · apply join (mid := 75005)
            · apply join (mid := 65005)
              · exact holdsBlocks (lo := 60005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 70005)
                · exact holdsBlocks (lo := 65005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 70005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 80005)
              · exact holdsBlocks (lo := 75005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 85005)
                · exact holdsBlocks (lo := 80005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 85005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 105005)
            · apply join (mid := 95005)
              · exact holdsBlocks (lo := 90005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 100005)
                · exact holdsBlocks (lo := 95005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 100005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 115005)
              · apply join (mid := 110005)
                · exact holdsBlocks (lo := 105005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 110005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 120005)
                · exact holdsBlocks (lo := 115005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 120005) (width := 100) (count := 50) (by decide +kernel)
      · apply join (mid := 185005)
        · apply join (mid := 155005)
          · apply join (mid := 140005)
            · apply join (mid := 130005)
              · exact holdsBlocks (lo := 125005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 135005)
                · exact holdsBlocks (lo := 130005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 135005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 145005)
              · exact holdsBlocks (lo := 140005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 150005)
                · exact holdsBlocks (lo := 145005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 150005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 170005)
            · apply join (mid := 160005)
              · exact holdsBlocks (lo := 155005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 165005)
                · exact holdsBlocks (lo := 160005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 165005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 175005)
              · exact holdsBlocks (lo := 170005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 180005)
                · exact holdsBlocks (lo := 175005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 180005) (width := 100) (count := 50) (by decide +kernel)
        · apply join (mid := 215005)
          · apply join (mid := 200005)
            · apply join (mid := 190005)
              · exact holdsBlocks (lo := 185005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 195005)
                · exact holdsBlocks (lo := 190005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 195005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 205005)
              · exact holdsBlocks (lo := 200005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 210005)
                · exact holdsBlocks (lo := 205005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 210005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 230005)
            · apply join (mid := 220005)
              · exact holdsBlocks (lo := 215005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 225005)
                · exact holdsBlocks (lo := 220005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 225005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 240005)
              · apply join (mid := 235005)
                · exact holdsBlocks (lo := 230005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 235005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 245005)
                · exact holdsBlocks (lo := 240005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 245005) (width := 100) (count := 50) (by decide +kernel)
    · apply join (mid := 375005)
      · apply join (mid := 310005)
        · apply join (mid := 280005)
          · apply join (mid := 265005)
            · apply join (mid := 255005)
              · exact holdsBlocks (lo := 250005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 260005)
                · exact holdsBlocks (lo := 255005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 260005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 270005)
              · exact holdsBlocks (lo := 265005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 275005)
                · exact holdsBlocks (lo := 270005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 275005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 295005)
            · apply join (mid := 285005)
              · exact holdsBlocks (lo := 280005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 290005)
                · exact holdsBlocks (lo := 285005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 290005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 300005)
              · exact holdsBlocks (lo := 295005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 305005)
                · exact holdsBlocks (lo := 300005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 305005) (width := 100) (count := 50) (by decide +kernel)
        · apply join (mid := 340005)
          · apply join (mid := 325005)
            · apply join (mid := 315005)
              · exact holdsBlocks (lo := 310005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 320005)
                · exact holdsBlocks (lo := 315005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 320005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 330005)
              · exact holdsBlocks (lo := 325005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 335005)
                · exact holdsBlocks (lo := 330005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 335005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 355005)
            · apply join (mid := 345005)
              · exact holdsBlocks (lo := 340005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 350005)
                · exact holdsBlocks (lo := 345005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 350005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 365005)
              · apply join (mid := 360005)
                · exact holdsBlocks (lo := 355005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 360005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 370005)
                · exact holdsBlocks (lo := 365005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 370005) (width := 100) (count := 50) (by decide +kernel)
      · apply join (mid := 435005)
        · apply join (mid := 405005)
          · apply join (mid := 390005)
            · apply join (mid := 380005)
              · exact holdsBlocks (lo := 375005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 385005)
                · exact holdsBlocks (lo := 380005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 385005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 395005)
              · exact holdsBlocks (lo := 390005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 400005)
                · exact holdsBlocks (lo := 395005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 400005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 420005)
            · apply join (mid := 410005)
              · exact holdsBlocks (lo := 405005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 415005)
                · exact holdsBlocks (lo := 410005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 415005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 425005)
              · exact holdsBlocks (lo := 420005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 430005)
                · exact holdsBlocks (lo := 425005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 430005) (width := 100) (count := 50) (by decide +kernel)
        · apply join (mid := 465005)
          · apply join (mid := 450005)
            · apply join (mid := 440005)
              · exact holdsBlocks (lo := 435005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 445005)
                · exact holdsBlocks (lo := 440005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 445005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 455005)
              · exact holdsBlocks (lo := 450005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 460005)
                · exact holdsBlocks (lo := 455005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 460005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 480005)
            · apply join (mid := 470005)
              · exact holdsBlocks (lo := 465005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 475005)
                · exact holdsBlocks (lo := 470005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 475005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 490005)
              · apply join (mid := 485005)
                · exact holdsBlocks (lo := 480005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 485005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 495005)
                · exact holdsBlocks (lo := 490005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 495005) (width := 100) (count := 50) (by decide +kernel)
  · apply join (mid := 750005)
    · apply join (mid := 625005)
      · apply join (mid := 560005)
        · apply join (mid := 530005)
          · apply join (mid := 515005)
            · apply join (mid := 505005)
              · exact holdsBlocks (lo := 500005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 510005)
                · exact holdsBlocks (lo := 505005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 510005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 520005)
              · exact holdsBlocks (lo := 515005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 525005)
                · exact holdsBlocks (lo := 520005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 525005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 545005)
            · apply join (mid := 535005)
              · exact holdsBlocks (lo := 530005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 540005)
                · exact holdsBlocks (lo := 535005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 540005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 550005)
              · exact holdsBlocks (lo := 545005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 555005)
                · exact holdsBlocks (lo := 550005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 555005) (width := 100) (count := 50) (by decide +kernel)
        · apply join (mid := 590005)
          · apply join (mid := 575005)
            · apply join (mid := 565005)
              · exact holdsBlocks (lo := 560005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 570005)
                · exact holdsBlocks (lo := 565005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 570005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 580005)
              · exact holdsBlocks (lo := 575005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 585005)
                · exact holdsBlocks (lo := 580005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 585005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 605005)
            · apply join (mid := 595005)
              · exact holdsBlocks (lo := 590005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 600005)
                · exact holdsBlocks (lo := 595005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 600005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 615005)
              · apply join (mid := 610005)
                · exact holdsBlocks (lo := 605005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 610005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 620005)
                · exact holdsBlocks (lo := 615005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 620005) (width := 100) (count := 50) (by decide +kernel)
      · apply join (mid := 685005)
        · apply join (mid := 655005)
          · apply join (mid := 640005)
            · apply join (mid := 630005)
              · exact holdsBlocks (lo := 625005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 635005)
                · exact holdsBlocks (lo := 630005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 635005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 645005)
              · exact holdsBlocks (lo := 640005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 650005)
                · exact holdsBlocks (lo := 645005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 650005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 670005)
            · apply join (mid := 660005)
              · exact holdsBlocks (lo := 655005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 665005)
                · exact holdsBlocks (lo := 660005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 665005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 675005)
              · exact holdsBlocks (lo := 670005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 680005)
                · exact holdsBlocks (lo := 675005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 680005) (width := 100) (count := 50) (by decide +kernel)
        · apply join (mid := 715005)
          · apply join (mid := 700005)
            · apply join (mid := 690005)
              · exact holdsBlocks (lo := 685005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 695005)
                · exact holdsBlocks (lo := 690005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 695005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 705005)
              · exact holdsBlocks (lo := 700005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 710005)
                · exact holdsBlocks (lo := 705005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 710005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 730005)
            · apply join (mid := 720005)
              · exact holdsBlocks (lo := 715005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 725005)
                · exact holdsBlocks (lo := 720005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 725005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 740005)
              · apply join (mid := 735005)
                · exact holdsBlocks (lo := 730005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 735005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 745005)
                · exact holdsBlocks (lo := 740005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 745005) (width := 100) (count := 50) (by decide +kernel)
    · apply join (mid := 875005)
      · apply join (mid := 810005)
        · apply join (mid := 780005)
          · apply join (mid := 765005)
            · apply join (mid := 755005)
              · exact holdsBlocks (lo := 750005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 760005)
                · exact holdsBlocks (lo := 755005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 760005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 770005)
              · exact holdsBlocks (lo := 765005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 775005)
                · exact holdsBlocks (lo := 770005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 775005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 795005)
            · apply join (mid := 785005)
              · exact holdsBlocks (lo := 780005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 790005)
                · exact holdsBlocks (lo := 785005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 790005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 800005)
              · exact holdsBlocks (lo := 795005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 805005)
                · exact holdsBlocks (lo := 800005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 805005) (width := 100) (count := 50) (by decide +kernel)
        · apply join (mid := 840005)
          · apply join (mid := 825005)
            · apply join (mid := 815005)
              · exact holdsBlocks (lo := 810005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 820005)
                · exact holdsBlocks (lo := 815005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 820005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 830005)
              · exact holdsBlocks (lo := 825005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 835005)
                · exact holdsBlocks (lo := 830005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 835005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 855005)
            · apply join (mid := 845005)
              · exact holdsBlocks (lo := 840005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 850005)
                · exact holdsBlocks (lo := 845005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 850005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 865005)
              · apply join (mid := 860005)
                · exact holdsBlocks (lo := 855005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 860005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 870005)
                · exact holdsBlocks (lo := 865005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 870005) (width := 100) (count := 50) (by decide +kernel)
      · apply join (mid := 940005)
        · apply join (mid := 905005)
          · apply join (mid := 890005)
            · apply join (mid := 880005)
              · exact holdsBlocks (lo := 875005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 885005)
                · exact holdsBlocks (lo := 880005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 885005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 895005)
              · exact holdsBlocks (lo := 890005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 900005)
                · exact holdsBlocks (lo := 895005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 900005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 920005)
            · apply join (mid := 910005)
              · exact holdsBlocks (lo := 905005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 915005)
                · exact holdsBlocks (lo := 910005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 915005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 930005)
              · apply join (mid := 925005)
                · exact holdsBlocks (lo := 920005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 925005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 935005)
                · exact holdsBlocks (lo := 930005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 935005) (width := 100) (count := 50) (by decide +kernel)
        · apply join (mid := 970005)
          · apply join (mid := 955005)
            · apply join (mid := 945005)
              · exact holdsBlocks (lo := 940005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 950005)
                · exact holdsBlocks (lo := 945005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 950005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 960005)
              · exact holdsBlocks (lo := 955005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 965005)
                · exact holdsBlocks (lo := 960005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 965005) (width := 100) (count := 50) (by decide +kernel)
          · apply join (mid := 985005)
            · apply join (mid := 975005)
              · exact holdsBlocks (lo := 970005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 980005)
                · exact holdsBlocks (lo := 975005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 980005) (width := 100) (count := 50) (by decide +kernel)
            · apply join (mid := 995005)
              · apply join (mid := 990005)
                · exact holdsBlocks (lo := 985005) (width := 100) (count := 50) (by decide +kernel)
                · exact holdsBlocks (lo := 990005) (width := 100) (count := 50) (by decide +kernel)
              · apply join (mid := 999905)
                · exact holdsBlocks (lo := 995005) (width := 100) (count := 49) (by decide +kernel)
                · exact holdsFrom (lo := 999905) (k := 96) (by decide +kernel)

end OMA.DivisorWitness

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1_H2_R1.H1 := by
  intro q hq h5 hmax
  have h := OMA.DivisorWitness.checked q h5 (by omega)
  unfold OMA.DivisorWitness.check at h
  rw [OMA.DivisorWitness.skip_prime hq, Bool.false_or] at h
  exact OMA.DivisorWitness.search_sound h
