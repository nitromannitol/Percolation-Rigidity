import Rigidity.Proofs.Partition.GeneralCount
import Rigidity.Percolation.TriadicGoodJointIndependence

/-!
# Minimal scales for general partitions: probability

Let `G` be a random collection of good triadic cubes whose failure events `{T ∉ G}` are determined
by the open edges inside the threefold enlargement of `T` (Armstrong and Dario, (2.1)) and have
probability at most `C exp(-c 3^{n s})` for cubes of scale `n` ((2.2)). Failure events of cubes with
disjoint enlargements are independent, so at least `k` failures in a separated family of `N`
cubes, each failing with probability at most `a`, have probability at most `(e N a / k)^k`; a
failure of scale at least `J` near the cube of scale `m` centred at the origin has probability at
most `25ᵈ 3^{d m} C exp(-c 3^{J s}) ∑_k exp(-c (3^s - 1))^k`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

open scoped Classical in
/-- **Many failures in a separated family** (general good cubes). -/
theorem measure_le_card_notMem_le (p : unitInterval) (G : Configuration d → Set (TriadicCube d))
    (hloc : ∀ T : TriadicCube d,
      MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {ι : Type*} (Q : ι → TriadicCube d)
    (hsep : Pairwise fun i j => Disjoint (Q i).centeredTriple (Q j).centeredTriple)
    (s : Finset ι) (q : ℝ≥0∞) (hq : ∀ i ∈ s, latticeBondLaw d p {ω | Q i ∉ G ω} ≤ q) (k : ℕ) :
    latticeBondLaw d p {ω | k ≤ (s.filter fun i => Q i ∉ G ω).card} ≤
      (s.card.choose k : ℝ≥0∞) * q ^ k := by
  have hsub : {ω | k ≤ (s.filter fun i => Q i ∉ G ω).card} ⊆
      ⋃ S ∈ s.powersetCard k, ⋂ i ∈ S, {ω | Q i ∉ G ω} := by
    intro ω hω
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hω
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq, exists_prop]
    exact ⟨S, Finset.mem_powersetCard.2 ⟨hS.trans (Finset.filter_subset _ _), hcard⟩,
      fun i hi => (Finset.mem_filter.1 (hS hi)).2⟩
  calc _ ≤ latticeBondLaw d p (⋃ S ∈ s.powersetCard k, ⋂ i ∈ S, {ω | Q i ∉ G ω}) :=
        measure_mono hsub
    _ ≤ ∑ S ∈ s.powersetCard k, latticeBondLaw d p (⋂ i ∈ S, {ω | Q i ∉ G ω}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _S ∈ s.powersetCard k, q ^ k := by
        refine Finset.sum_le_sum fun S hS => ?_
        have hS' := Finset.mem_powersetCard.1 hS
        rw [(iIndep_localEdgeSigma p (fun i => (Q i).centeredTriple) hsep).meas_biInter
          (fun i _ => hloc (Q i))]
        calc ∏ i ∈ S, latticeBondLaw d p {ω | Q i ∉ G ω} ≤ ∏ _i ∈ S, q :=
              Finset.prod_le_prod' fun i hi => hq i (hS'.1 hi)
          _ = q ^ k := by rw [Finset.prod_const, hS'.2]
    _ = (s.card.choose k : ℝ≥0∞) * q ^ k := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- **Many failures in a residue class** (general good cubes): if every cube of scale `j` fails
with probability at most `a`, then at least `k > 0` failures of a residue class near the cube of
scale `m` occur with probability at most `(e N a / k)^k`, `N = (2 · 3^{m-j} + 23)^d`. -/
theorem measure_le_classCount_le (p : unitInterval) (G : Configuration d → Set (TriadicCube d))
    (hloc : ∀ T : TriadicCube d,
      MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {a : ℝ} (ha : 0 ≤ a) {m j : ℕ}
    (hq : ∀ ι : Fin d → ℤ,
      latticeBondLaw d p {ω | (⟨j, ι⟩ : TriadicCube d) ∉ G ω} ≤ ENNReal.ofReal a)
    (r : Fin d → Fin 3) {k : ℕ} (hk : 0 < k) :
    latticeBondLaw d p {ω | k ≤ classCount (fun T => T ∉ G ω) m j r} ≤
      ENNReal.ofReal ((Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / k) ^ k) := by
  classical
  set s := (nearIndices d m j).subtype fun ι => residue ι = r with hsdef
  have hsep : Pairwise fun ι ι' : {ι : Fin d → ℤ // residue ι = r} =>
      Disjoint (⟨j, ι.1⟩ : TriadicCube d).centeredTriple
        (⟨j, ι'.1⟩ : TriadicCube d).centeredTriple := by
    intro ι ι' hne
    exact disjoint_centeredTriple_of_residue_eq (fun h => hne (Subtype.ext h))
      (ι.2.trans ι'.2.symm)
  have h := measure_le_card_notMem_le p G hloc (fun ι : {ι : Fin d → ℤ // residue ι = r} =>
    (⟨j, ι.1⟩ : TriadicCube d)) hsep s (ENNReal.ofReal a) (fun ι _ => hq ι.1) k
  have hscard : (s.card : ℝ) ≤ (2 * (3 : ℝ) ^ (m - j) + 23) ^ d := by
    rw [← card_nearIndices d m j]
    have : s.card ≤ (nearIndices d m j).card := by
      rw [hsdef, Finset.card_subtype]
      exact Finset.card_filter_le _ _
    exact_mod_cast this
  have hreal : ((s.card.choose k : ℕ) : ℝ) * a ^ k ≤
      (Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / k) ^ k := by
    refine (choose_mul_pow_le s.card k hk ha).trans ?_
    gcongr
  simp only [classCount]
  refine h.trans ?_
  rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Many failures in a residue class at a large scale** occur with probability at most
`exp(-3^{e})`, `e = d (m - j) - (τ + 1)(j + 1)`. -/
theorem measure_classCount_ge_le (p : unitInterval) (G : Configuration d → Set (TriadicCube d))
    (hloc : ∀ T : TriadicCube d,
      MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {C1 c s0 : ℝ} (hC1 : 0 ≤ C1)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ G ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0))) {m j τ : ℕ}
    (hj : Real.exp 1 * 25 ^ d * C1 * (3 : ℝ) ^ ((τ + 1) * (j + 1)) *
      Real.exp (-c * ((3 : ℝ) ^ j) ^ s0) ≤ Real.exp (-1))
    (hexp : (τ + 1) * (j + 1) ≤ d * (m - j)) (r : Fin d → Fin 3) :
    latticeBondLaw d p {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤
        classCount (fun T => T ∉ G ω) m j r} ≤
      ENNReal.ofReal (Real.exp (-(3 : ℝ) ^ (d * (m - j) - (τ + 1) * (j + 1)))) := by
  set e := d * (m - j) - (τ + 1) * (j + 1) with hedef
  set a : ℝ := C1 * Real.exp (-c * ((3 : ℝ) ^ j) ^ s0) with hadef
  have ha : 0 ≤ a := by positivity
  have hk : 0 < 3 ^ e := by positivity
  have h := measure_le_classCount_le p G hloc ha (m := m) (fun ι => hq _) r hk
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hde : d * (m - j) = e + (τ + 1) * (j + 1) := by omega
  have hN : (2 * (3 : ℝ) ^ (m - j) + 23) ^ d ≤ 25 ^ d * (3 ^ e * 3 ^ ((τ + 1) * (j + 1))) := by
    have h1 : (1 : ℝ) ≤ 3 ^ (m - j) := one_le_pow₀ (by norm_num)
    calc (2 * (3 : ℝ) ^ (m - j) + 23) ^ d ≤ (25 * 3 ^ (m - j)) ^ d := by gcongr; linarith
      _ = 25 ^ d * 3 ^ (d * (m - j)) := by rw [mul_pow, ← pow_mul, mul_comm (m - j) d]
      _ = _ := by rw [hde, pow_add]
  have hbase : Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ) ≤
      Real.exp (-1) := by
    have hpos : (0 : ℝ) < ((3 ^ e : ℕ) : ℝ) := by exact_mod_cast hk
    rw [div_le_iff₀ hpos]
    have hcast : ((3 ^ e : ℕ) : ℝ) = 3 ^ e := by push_cast; ring
    rw [hcast]
    calc Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a
        ≤ Real.exp 1 * (25 ^ d * (3 ^ e * 3 ^ ((τ + 1) * (j + 1)))) * a := by gcongr
      _ = (Real.exp 1 * 25 ^ d * C1 * (3 : ℝ) ^ ((τ + 1) * (j + 1)) *
            Real.exp (-c * ((3 : ℝ) ^ j) ^ s0)) * 3 ^ e := by rw [hadef]; ring
      _ ≤ Real.exp (-1) * 3 ^ e := mul_le_mul_of_nonneg_right hj (by positivity)
  have hb0 : 0 ≤ Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ) := by
    positivity
  calc (Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ)) ^ (3 ^ e)
      ≤ Real.exp (-1) ^ (3 ^ e) := pow_le_pow_left₀ hb0 hbase _
    _ = Real.exp (-(3 : ℝ) ^ e) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- **A large failure near the cube of scale `m`** (general good cubes) occurs with probability at
most `25ᵈ 3^{d m} C exp(-c 3^{J s}) ∑_k exp(-c (3^s - 1))^k`. -/
theorem measure_exists_notMem_near_le (p : unitInterval) (G : Configuration d → Set (TriadicCube d))
    {C1 c s0 : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c) (hs0 : 0 < s0)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ G ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0))) (m J : ℕ) :
    latticeBondLaw d p {ω | ∃ T : TriadicCube d, J ≤ T.scale ∧ T ∉ G ω ∧
        ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} ≤
      ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) *
        ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ s0) ^ J)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ s0 - 1))) ^ k := by
  classical
  let B : ℕ → Set (Configuration d) := fun n =>
    ⋃ ι ∈ nearIndices d m n, {ω | (⟨n, ι⟩ : TriadicCube d) ∉ G ω}
  have hsub : {ω | ∃ T : TriadicCube d, J ≤ T.scale ∧ T ∉ G ω ∧
      ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} ⊆
      {ω | ∃ n : ℕ, J ≤ n ∧ ω ∈ B n} := by
    rintro ω ⟨T, hJ, hbad, x, hx, hnear⟩
    refine ⟨T.scale, hJ, ?_⟩
    simp only [B, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨T.index, index_mem_nearIndices hx hnear, hbad⟩
  have hB : ∀ n : ℕ, latticeBondLaw d p (B n) ≤
      ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) *
        ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ s0) ^ n)) := by
    intro n
    have hcomm : ((3 : ℝ) ^ n) ^ s0 = ((3 : ℝ) ^ s0) ^ n :=
      (Real.rpow_pow_comm (show (0 : ℝ) ≤ 3 by norm_num) s0 n).symm
    have hcard : ((nearIndices d m n).card : ℝ) ≤ 25 ^ d * 3 ^ (d * m) := by
      rw [card_nearIndices]
      have h1 : (1 : ℝ) ≤ 3 ^ (m - n) := one_le_pow₀ (by norm_num)
      have h2 : (3 : ℝ) ^ (m - n) ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      calc (2 * (3 : ℝ) ^ (m - n) + 23) ^ d ≤ (25 * 3 ^ m) ^ d := by gcongr; linarith
        _ = 25 ^ d * 3 ^ (d * m) := by rw [mul_pow, ← pow_mul, mul_comm m d]
    calc latticeBondLaw d p (B n)
        ≤ ∑ ι ∈ nearIndices d m n, latticeBondLaw d p {ω | (⟨n, ι⟩ : TriadicCube d) ∉ G ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _ι ∈ nearIndices d m n,
            ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ s0) ^ n)) :=
          Finset.sum_le_sum fun ι _ => by
            have := hq (⟨n, ι⟩ : TriadicCube d)
            rwa [show (⟨n, ι⟩ : TriadicCube d).scale = n from rfl, hcomm] at this
      _ = ENNReal.ofReal ((nearIndices d m n).card *
            (C1 * Real.exp (-c * ((3 : ℝ) ^ s0) ^ n))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * ((3 : ℝ) ^ s0) ^ n)) := by
          apply ENNReal.ofReal_le_ofReal
          have he : 0 ≤ C1 * Real.exp (-c * ((3 : ℝ) ^ s0) ^ n) := by positivity
          calc ((nearIndices d m n).card : ℝ) * (C1 * Real.exp (-c * ((3 : ℝ) ^ s0) ^ n))
              ≤ 25 ^ d * 3 ^ (d * m) * (C1 * Real.exp (-c * ((3 : ℝ) ^ s0) ^ n)) :=
                mul_le_mul_of_nonneg_right hcard he
            _ = _ := by ring
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]
  exact (measure_mono hsub).trans
    (measure_exists_large_index_le_stretched _ B _ ((3 : ℝ) ^ s0) c
      (Real.one_lt_rpow (by norm_num) hs0) hc hB J)

/-- The threshold scale for stretched exponents: beyond it,
`A 3^{k (j + 1)} exp(-c 3^{j s}) ≤ e⁻¹`. -/
theorem exists_large_scale_exp_rpow_le (A c s0 : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (hs0 : 0 < s0)
    (k : ℕ) :
    ∃ j0 : ℕ, ∀ j, j0 ≤ j →
      A * (3 : ℝ) ^ (k * (j + 1)) * Real.exp (-c * ((3 : ℝ) ^ j) ^ s0) ≤ Real.exp (-1) := by
  set N : ℕ := ⌈(k : ℝ) / s0⌉₊ with hNdef
  set B : ℝ := A * 3 ^ k * ((N.factorial : ℝ) / (c / 2) ^ N) with hBdef
  have hB : 0 ≤ B := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((2 / c) * (1 + B))
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hs0)
  refine ⟨n, fun j hj => ?_⟩
  set y : ℝ := ((3 : ℝ) ^ j) ^ s0 with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hs0.le
  have hy0 : 0 ≤ y := by linarith
  have hyn : (2 / c) * (1 + B) < y := by
    rw [hydef, ← Real.rpow_pow_comm (show (0 : ℝ) ≤ 3 by norm_num)]
    exact hn.trans_le (pow_le_pow_right₀ (Real.one_le_rpow (by norm_num) hs0.le) hj)
  have hkN : (k : ℝ) ≤ s0 * N := by
    have h := Nat.le_ceil ((k : ℝ) / s0)
    rw [div_le_iff₀ hs0] at h
    linarith
  have hpowk : ((3 : ℝ) ^ j) ^ k ≤ y ^ N := by
    have e1 : ((3 : ℝ) ^ j) ^ k = ((3 : ℝ) ^ j) ^ ((k : ℕ) : ℝ) := (Real.rpow_natCast _ k).symm
    have e2 : y ^ N = (((3 : ℝ) ^ j) ^ s0) ^ ((N : ℕ) : ℝ) := by
      rw [hydef]; exact (Real.rpow_natCast _ N).symm
    have e3 : (((3 : ℝ) ^ j) ^ s0) ^ ((N : ℕ) : ℝ) = ((3 : ℝ) ^ j) ^ (s0 * N) :=
      (Real.rpow_mul (by positivity) _ _).symm
    rw [e1, e2, e3]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)) hkN
  have h1 : (3 : ℝ) ^ (k * (j + 1)) = 3 ^ k * ((3 : ℝ) ^ j) ^ k := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have h2 := pow_mul_exp_neg_le N hc hy0
  have h3 : A * (3 : ℝ) ^ (k * (j + 1)) * Real.exp (-c * y) ≤ B * Real.exp (-(c / 2) * y) := by
    rw [h1, hBdef]
    have hA3 : 0 ≤ A * 3 ^ k := by positivity
    calc A * (3 ^ k * ((3 : ℝ) ^ j) ^ k) * Real.exp (-c * y)
        ≤ A * (3 ^ k * y ^ N) * Real.exp (-c * y) := by gcongr
      _ = A * 3 ^ k * (y ^ N * Real.exp (-c * y)) := by ring
      _ ≤ A * 3 ^ k * ((N.factorial : ℝ) / (c / 2) ^ N * Real.exp (-(c / 2) * y)) :=
          mul_le_mul_of_nonneg_left h2 hA3
      _ = _ := by ring
  have h4 : -(c / 2) * y ≤ -(1 + B) := by
    have : (c / 2) * ((2 / c) * (1 + B)) = 1 + B := by field_simp
    nlinarith
  have h5 : B * Real.exp (-(c / 2) * y) ≤ B * Real.exp (-(1 + B)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h4) hB
  have h6 : B * Real.exp (-(1 + B)) ≤ Real.exp (-1) := by
    have hexp : Real.exp (-(1 + B)) = Real.exp (-1) * Real.exp (-B) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    have hBe : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
    have hBe' : B * Real.exp (-B) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos B)]
      exact hBe
    have he : 0 < Real.exp (-1) := Real.exp_pos _
    nlinarith
  exact h3.trans (h5.trans h6)

/-- A polynomial factor against an exponential: if `0 ≤ x ≤ 3 y` and `P ≤ x^N`, then
`P exp(-c y) ≤ (N! / (c/6)^N) exp(-(c/6) x)`. -/
theorem mul_exp_neg_le_of_le_pow {P x y c : ℝ} {N : ℕ} (hx0 : 0 ≤ x) (hP : P ≤ x ^ N)
    (hxy : x ≤ 3 * y) (hc : 0 < c) :
    P * Real.exp (-c * y) ≤
      ((N.factorial : ℝ) / (c / 3 / 2) ^ N) * Real.exp (-(c / 3 / 2) * x) := by
  have hexp : Real.exp (-c * y) ≤ Real.exp (-(c / 3) * x) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hpow := pow_mul_exp_neg_le N (show 0 < c / 3 by positivity) hx0
  calc P * Real.exp (-c * y) ≤ x ^ N * Real.exp (-(c / 3) * x) := by
        gcongr
    _ ≤ _ := hpow

end Rigidity.Percolation
