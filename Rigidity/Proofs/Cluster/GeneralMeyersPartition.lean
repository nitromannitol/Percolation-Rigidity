import Rigidity.Proofs.Cluster.GeneralRHPartition

/-!
# The partition `𝓠_a` of Definition 3.9 of Armstrong and Dario, in every dimension

Armstrong and Dario (Definition 3.9) apply Proposition 2.1 to the family of the cubes on which a
deterministic Meyers estimate holds, with the exponent `ε` and the constant `C` of
Proposition 3.8, and call `𝓠_a` the resulting partition, with its minimal scales `𝓜_t(𝓠_a)`
and their tails (3.21). As for the partition `𝓡` of
Definition 3.7 (`GeneralRHPartition`), a cube `□ = cube k x` satisfies the Meyers estimate
(`MeyersCube ε C ω k x`) when for every set `U₀ ⊆ 3□` closed under the open edges inside `3□` and
every function `u` harmonic at the points of `U₀` all of whose open edges stay in `U₀`,
`avg_□ |∇u 1_{𝐚≠0}|^{2+ε} ≤ C (avg_{3□} |∇u 1_{𝐚≠0}|²)^{1+ε/2}`; a triadic cube of positive scale is
good (`meyersGood`) when the estimate holds on each of its children, and cubes of scale zero are
good. The estimate on a child reads only the open edges at the points of its triple and their
lattice neighbours, so the failure event of `T` belongs to the σ-algebra of the open edges inside
`3T` (`measurableSet_not_mem_meyersGood_local`), the hypothesis (2.1) of Proposition 2.1.

The failure bound (2.2) for this family is (3.17) of Armstrong and Dario
(`exists_meyersFailureBound`): by Proposition 3.8 above the partition `𝓡`
(`meyers_rh_uniform`), the estimate holds on `cube k x` as soon as the cells of `𝓡` meeting the
triple are of scale at most `k` and `∑_{cube k x} size^t ≤ K |cube k x|`, and by Propositions 2.1
and 2.4 for `𝓡` both fail with stretched-exponentially small probability
(`exists_measure_stoppingScale_large_le`, for any local family with the bound (2.2)).
Propositions 2.1 and 2.4 applied to `meyersGood` give the partition `𝓠_a` with its minimal scales
(`meyersPartition_holds`).
-/

namespace Rigidity.Proofs.Cluster.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal

variable {d : ℕ}

section Tails

/-- A factor `|3□| = 3^{d(k+1)}` is absorbed by a stretched exponential in `3^k`. -/
theorem exists_card_enl_mul_exp_le_exp {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ((3 : ℝ) ^ (k + 1)) ^ d * Real.exp (-a * ((3 : ℝ) ^ k) ^ s) ≤
      K * Real.exp (-(a / 2) * ((3 : ℝ) ^ k) ^ s) := by
  obtain ⟨K, hK, h⟩ := exists_exp_neg_rpow_le_inv_pow (c := a / 2) (by positivity) hs d
  refine ⟨3 ^ d * K, by positivity, fun k => ?_⟩
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  set X := ((3 : ℝ) ^ k) ^ s with hX
  have hsplit : Real.exp (-a * X) = Real.exp (-(a / 2) * X) * Real.exp (-(a / 2) * X) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e : ((3 : ℝ) ^ (k + 1)) ^ d = 3 ^ d * ((3 : ℝ) ^ k) ^ d := by
    rw [pow_succ, mul_pow, mul_comm]
  have hb : ((3 : ℝ) ^ k) ^ d * Real.exp (-(a / 2) * X) ≤ K := by
    calc ((3 : ℝ) ^ k) ^ d * Real.exp (-(a / 2) * X)
        ≤ ((3 : ℝ) ^ k) ^ d * (K * ((3 : ℝ) ^ k)⁻¹ ^ d) :=
          mul_le_mul_of_nonneg_left (h k) (by positivity)
      _ = K * (((3 : ℝ) ^ k) ^ d * ((3 : ℝ) ^ k)⁻¹ ^ d) := by ring
      _ = K := by rw [← mul_pow, mul_inv_cancel₀ h3.ne', one_pow, mul_one]
  rw [e, hsplit]
  calc 3 ^ d * ((3 : ℝ) ^ k) ^ d * (Real.exp (-(a / 2) * X) * Real.exp (-(a / 2) * X))
      = 3 ^ d * (((3 : ℝ) ^ k) ^ d * Real.exp (-(a / 2) * X)) * Real.exp (-(a / 2) * X) := by
        ring
    _ ≤ 3 ^ d * K * Real.exp (-(a / 2) * X) := by gcongr

/-- **Minimal scales with stretched-exponential tails** (Armstrong and Dario, Propositions 2.1 and
2.4, for a local family with the bound (2.2)). The cells of the partition meeting the triple of
`cube k y` have scale at most `k`, and `∑_{x ∈ cube k y} size(cell(x))^τ ≤ K |cube k y|`, off an
event of probability at most `C exp(-c 3^{k r})`. -/
theorem exists_measure_stoppingScale_large_le (hd : 0 < d) (p : unitInterval)
    (G : Configuration d → Set (TriadicCube d))
    (hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω})
    (hloc : ∀ T : TriadicCube d, MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {C1 c s0 : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c) (hs0 : 0 < s0) (hs1 : s0 ≤ 1)
    (hfail : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ G ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)))
    (τ : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C2 c2 r : ℝ, 0 ≤ C2 ∧ 0 < c2 ∧ 0 < r ∧ r ≤ 1 ∧
      ∀ (k : ℕ) (y : Vertex d),
      latticeBondLaw d p {ω | (∃ z ∈ enl 1 k y, k < stoppingScale (G ω) z) ∨
          K * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ stoppingScale (G ω) x) ^ τ} ≤
        ENNReal.ofReal (C2 * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r)) := by
  set μ := latticeBondLaw d p with hμ
  obtain ⟨hae, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates_general hd μ G hGm hC1 hc hs0 hfail
  obtain ⟨Cfin, Ctot, hCtot, c', hc', hsum⟩ :=
    exists_measure_sum_stoppingSize_gt_le hd p G hGm hloc hC1 hc hs0 hs1 hfail τ
  set r : ℝ := s0 / ((2 * (d + τ + 1) : ℕ) : ℝ) with hr
  have hr0 : 0 < r := by positivity
  have hrs0 : r ≤ s0 := by
    rw [hr]
    refine div_le_self hs0.le ?_
    have : (1 : ℕ) ≤ 2 * (d + τ + 1) := by omega
    exact_mod_cast this
  set a : ℝ := θ⁻¹ ^ s0 with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨K1, hK1, hK1k⟩ := exists_card_enl_mul_exp_le_exp (d := d) ha0 hs0
  set c2 : ℝ := min (a / 2) c' with hc2
  have hc20 : 0 < c2 := lt_min (by positivity) hc'
  refine ⟨max Cfin 0, le_max_right _ _, 2 * K1 + Ctot.toReal, c2, r, by positivity, hc20, hr0,
    hrs0.trans hs1, fun k y => ?_⟩
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hXr : ((3 : ℝ) ^ k) ^ r ≤ ((3 : ℝ) ^ k) ^ s0 :=
    Real.rpow_le_rpow_of_exponent_le h3k hrs0
  have hXr0 : 0 ≤ ((3 : ℝ) ^ k) ^ r := by positivity
  set R : TriadicCube d := ⟨k, idx k y⟩ with hR
  have hverts : R.toIntegerCube.vertices = cube k y := Finset.ext fun x => by
    rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
  set N₀ := {ω : Configuration d | ¬ ∀ x : Vertex d,
    ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)} with hN₀
  have hN₀0 : μ N₀ = 0 := ae_iff.1 hae
  set E₁ := ⋃ z ∈ enl 1 k y, {ω : Configuration d |
    (3 : ℝ) ^ k < TriadicCube.stoppingSize (G ω) z} with hE₁
  set E₂ := {ω : Configuration d | Cfin * 3 ^ (d * R.scale) <
    ∑ x ∈ R.toIntegerCube.vertices, TriadicCube.stoppingSize (G ω) x ^ τ} with hE₂
  have hsub : {ω | (∃ z ∈ enl 1 k y, k < stoppingScale (G ω) z) ∨
      max Cfin 0 * (cube k y).card <
        ∑ x ∈ cube k y, ((3 : ℝ) ^ stoppingScale (G ω) x) ^ τ} ⊆ N₀ ∪ (E₁ ∪ E₂) := by
    intro ω hω
    by_cases hu : ∀ x : Vertex d, ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)
    · right
      rcases hω with ⟨z, hz, hkz⟩ | hω
      · left
        refine Set.mem_biUnion hz ?_
        change (3 : ℝ) ^ k < TriadicCube.stoppingSize (G ω) z
        rw [stoppingSize_eq_stoppingScale hu]
        exact pow_lt_pow_right₀ (by norm_num) hkz
      · right
        change Cfin * 3 ^ (d * k) < _
        rw [hverts]
        have hcard : ((cube k y).card : ℝ) = (3 : ℝ) ^ (d * k) := by
          rw [card_cube, ← pow_mul, mul_comm]
        have h1 : ∑ x ∈ cube k y, ((3 : ℝ) ^ stoppingScale (G ω) x) ^ τ =
            ∑ x ∈ cube k y, TriadicCube.stoppingSize (G ω) x ^ τ :=
          Finset.sum_congr rfl fun x _ => by rw [stoppingSize_eq_stoppingScale hu]
        have h2 : Cfin * (3 : ℝ) ^ (d * k) ≤ max Cfin 0 * ((cube k y).card : ℝ) := by
          rw [hcard]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        linarith
    · left
      exact hu
  have hE₁ : μ E₁ ≤ ENNReal.ofReal (2 * K1 * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r)) := by
    have hz : ∀ z, μ {ω : Configuration d | (3 : ℝ) ^ k < TriadicCube.stoppingSize (G ω) z} ≤
        ENNReal.ofReal (2 * Real.exp (-a * ((3 : ℝ) ^ k) ^ s0)) := by
      intro z
      refine (measure_lt_le_of_exp_rpow_moment μ hθ hs0 (hmom z).1 (hmom z).2
        (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [Real.div_rpow (by positivity) hθ.le]
      apply le_of_eq
      congr 2
      rw [ha, Real.inv_rpow hθ.le]
      field_simp
    calc μ E₁ ≤ ∑ z ∈ enl 1 k y, μ {ω : Configuration d |
          (3 : ℝ) ^ k < TriadicCube.stoppingSize (G ω) z} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ enl 1 k y, ENNReal.ofReal (2 * Real.exp (-a * ((3 : ℝ) ^ k) ^ s0)) :=
          Finset.sum_le_sum fun z _ => hz z
      _ = ENNReal.ofReal (((enl 1 k y).card : ℝ) *
            (2 * Real.exp (-a * ((3 : ℝ) ^ k) ^ s0))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [card_enl]
          have h1 := hK1k k
          have h2 : Real.exp (-(a / 2) * ((3 : ℝ) ^ k) ^ s0) ≤
              Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r) := by
            refine Real.exp_le_exp.2 ?_
            have hm : c2 ≤ a / 2 := min_le_left _ _
            have : c2 * ((3 : ℝ) ^ k) ^ r ≤ a / 2 * ((3 : ℝ) ^ k) ^ s0 :=
              mul_le_mul hm hXr hXr0 (by positivity)
            linarith
          nlinarith [Real.exp_pos (-a * ((3 : ℝ) ^ k) ^ s0)]
  have hE₂ : μ E₂ ≤ ENNReal.ofReal (Ctot.toReal * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r)) := by
    refine (hsum R).trans ?_
    conv_lhs => rw [← ENNReal.ofReal_toReal hCtot]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      ENNReal.toReal_nonneg)
    have hm : c2 ≤ c' := min_le_right _ _
    have : c2 * ((3 : ℝ) ^ k) ^ r ≤ c' * ((3 : ℝ) ^ k) ^ r :=
      mul_le_mul_of_nonneg_right hm hXr0
    show -c' * ((3 : ℝ) ^ k) ^ r ≤ -c2 * ((3 : ℝ) ^ k) ^ r
    linarith
  calc μ _ ≤ μ (N₀ ∪ (E₁ ∪ E₂)) := measure_mono hsub
    _ ≤ μ N₀ + (μ E₁ + μ E₂) := (measure_union_le _ _).trans (add_le_add le_rfl
        (measure_union_le _ _))
    _ ≤ 0 + (ENNReal.ofReal (2 * K1 * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r)) +
          ENNReal.ofReal (Ctot.toReal * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r))) := by
        rw [hN₀0]
        exact add_le_add le_rfl (add_le_add hE₁ hE₂)
    _ = ENNReal.ofReal ((2 * K1 + Ctot.toReal) * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r)) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Tails

section Local

/-- **The Meyers estimate on `cube k x`** for every set of the triple closed under its open edges
and every function harmonic on it, with exponent `ε` and constant `C` (Armstrong and Dario,
Proposition 3.8, and the quantity `ME_ε(□)` before it). -/
def MeyersCube (ε C : ℝ) (ω : Configuration d) (k : ℕ) (x : Vertex d) : Prop :=
  ∀ U₀ : Finset (Vertex d), U₀ ⊆ enl 1 k x →
    (∀ z ∈ U₀, ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k x → w ∈ U₀) →
    ∀ u : Vertex d → ℝ,
      (∀ z ∈ U₀, (∀ w, (openGraph ω).Adj z w → w ∈ U₀) → openLaplacian ω u z = 0) →
      avg (cube k x) (fun z => clusterEnergy ω U₀ u z ^ (1 + ε / 2)) ≤
        C * avg (enl 1 k x) (clusterEnergy ω U₀ u) ^ (1 + ε / 2)

/-- **The local family of good cubes for the Meyers estimate** (Definition 3.9 of Armstrong and
Dario): the cubes of scale zero, and the cubes of positive scale on each of whose children
`MeyersCube` holds. -/
def meyersGood (ε C : ℝ) (ω : Configuration d) : Set (TriadicCube d) :=
  {T | ∀ k : ℕ, T.scale = k + 1 → ∀ x ∈ T.vertices, MeyersCube ε C ω k x}

variable {ω ω' : Configuration d}

/-- One direction of the locality of `MeyersCube`. -/
theorem meyersCube_of_adj_iff {ε C : ℝ} {k : ℕ} {x : Vertex d}
    (h : ∀ z ∈ enl 1 k x, ∀ w, ((openGraph ω').Adj z w ↔ (openGraph ω).Adj z w))
    (hω : MeyersCube ε C ω k x) : MeyersCube ε C ω' k x := by
  intro U₀ hU hcl u hu
  have hcl' : ∀ z ∈ U₀, ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k x → w ∈ U₀ :=
    fun z hz w hadj hw => hcl z hz w ((h z (hU hz) w).2 hadj) hw
  have hu' : ∀ z ∈ U₀, (∀ w, (openGraph ω).Adj z w → w ∈ U₀) → openLaplacian ω u z = 0 := by
    intro z hz hall
    rw [← openLaplacian_eq_of_adj_iff (h z (hU hz))]
    exact hu z hz fun w hw => hall w ((h z (hU hz) w).1 hw)
  have hE : ∀ z ∈ enl 1 k x, clusterEnergy ω' U₀ u z = clusterEnergy ω U₀ u z :=
    fun z hz => clusterEnergy_eq_of_adj_iff (h z hz) U₀ u
  have h1 := hω U₀ hU hcl' u hu'
  have e1 : avg (cube k x) (fun z => clusterEnergy ω' U₀ u z ^ (1 + ε / 2)) =
      avg (cube k x) (fun z => clusterEnergy ω U₀ u z ^ (1 + ε / 2)) := by
    unfold avg
    congr 1
    exact Finset.sum_congr rfl fun z hz => by simp only [hE z (cube_subset_enl 1 k x hz)]
  have e2 : avg (enl 1 k x) (clusterEnergy ω' U₀ u) = avg (enl 1 k x) (clusterEnergy ω U₀ u) := by
    unfold avg
    rw [Finset.sum_congr rfl fun z hz => hE z hz]
  rw [e1, e2]
  exact h1

/-- **Locality of `MeyersCube`.** -/
theorem meyersCube_iff_of_adj_iff {ε C : ℝ} {k : ℕ} {x : Vertex d}
    (h : ∀ z ∈ enl 1 k x, ∀ w, ((openGraph ω').Adj z w ↔ (openGraph ω).Adj z w)) :
    MeyersCube ε C ω' k x ↔ MeyersCube ε C ω k x :=
  ⟨meyersCube_of_adj_iff fun z hz w => (h z hz w).symm, meyersCube_of_adj_iff h⟩

/-- **Locality of the good cubes**: membership of `T` depends only on the open edges between
vertices of its threefold enlargement. -/
theorem mem_meyersGood_iff_of_adj_iff {ε C : ℝ} {T : TriadicCube d}
    (hagree : ∀ a ∈ T.centeredTriple, ∀ b ∈ T.centeredTriple,
      ((openGraph ω').Adj a b ↔ (openGraph ω).Adj a b)) :
    T ∈ meyersGood ε C ω' ↔ T ∈ meyersGood ε C ω := by
  simp only [meyersGood, Set.mem_setOf_eq]
  refine forall_congr' fun k => forall_congr' fun hk => forall₂_congr fun x hx => ?_
  exact meyersCube_iff_of_adj_iff fun z hz w =>
    adj_iff_of_near hagree (fun w' hw' => mem_centeredTriple_of_near_enl hk hx hz hw') w

/-- **The hypothesis (2.1) of Proposition 2.1** for the good cubes of the Meyers estimate: the
failure event of `T` belongs to the σ-algebra of the open edges inside `3T`. -/
theorem measurableSet_not_mem_meyersGood_local (ε C : ℝ) (T : TriadicCube d) :
    MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ meyersGood ε C ω} := by
  refine localGraphSigma_le_localEdgeSigma _ T.finite_centeredTriple _ ?_
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{g | ∃ ω' : Configuration d, (openGraph ω').induce T.centeredTriple = g ∧
    T ∉ meyersGood ε C ω'}, MeasurableSpace.measurableSet_top, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ω', hind, hω'⟩
    intro hω
    apply hω'
    refine (mem_meyersGood_iff_of_adj_iff fun a ha b hb => ?_).2 hω
    have := congrArg (fun g : SimpleGraph T.centeredTriple => g.Adj ⟨a, ha⟩ ⟨b, hb⟩) hind
    simpa using this
  · intro hω
    exact ⟨ω, rfl, hω⟩

theorem measurableSet_mem_meyersGood (ε C : ℝ) (T : TriadicCube d) :
    MeasurableSet {ω : Configuration d | T ∈ meyersGood ε C ω} := by
  have h := localEdgeSigma_le _ _ (measurableSet_not_mem_meyersGood_local ε C T)
  have : {ω : Configuration d | T ∈ meyersGood ε C ω} = {ω | T ∉ meyersGood ε C ω}ᶜ := by
    ext ω; simp
  rw [this]
  exact h.compl

end Local

section FailureBound

/-- **The failure bound (2.2) for the good cubes of the Meyers estimate** (Armstrong and Dario,
(3.17)), in every dimension `d ≥ 2`: for the exponent `ε` and the constant `C` of Proposition 3.8
above the partition `𝓡`, a triadic cube of scale `n` fails to be good with probability at most
`C₁ exp(-c 3^{n s})`. -/
theorem exists_meyersFailureBound [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∃ C1 c s0 : ℝ, 0 ≤ C1 ∧ 0 < c ∧ 0 < s0 ∧ s0 ≤ 1 ∧
      ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ meyersGood ε C ω} ≤
        ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)) := by
  have hd0 : 0 < d := by omega
  set μ := latticeBondLaw d p with hμ
  obtain ⟨A₀, hq⟩ := rhFailureBound_holds hd hpc
  obtain ⟨C1, c, s0, hC1, hc, hs0, hs1, hfail⟩ := hq
  set G : Configuration d → Set (TriadicCube d) := rhGood A₀ with hG
  have hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω} := measurableSet_mem_rhGood A₀
  have hloc := measurableSet_not_mem_rhGood_local (d := d) A₀
  obtain ⟨hae, -, -⟩ := partition_estimates_general hd0 μ G hGm hC1 hc hs0 hfail
  obtain ⟨ε, hε, t, ht, hM⟩ := meyers_rh_uniform (d := d) hd0 A₀
  set τ : ℕ := ⌈t⌉₊ with hτ
  have htτ : t ≤ τ := Nat.le_ceil t
  obtain ⟨K, hK, C2, c2, r, hC2, hc2, hr0, hr1, htail⟩ :=
    exists_measure_stoppingScale_large_le hd0 p G hGm hloc hC1 hc hs0 hs1 hfail τ
  obtain ⟨CM, hCM, hMK⟩ := hM K hK
  obtain ⟨K3, hK3, hK3k⟩ := exists_card_enl_mul_exp_le_exp (d := d) hc2 hr0
  refine ⟨ε, CM, hε, hCM, K3 * C2, c2 / 2 / 3 ^ r, r, by positivity, by positivity, hr0, hr1,
    fun T => ?_⟩
  set N₀ := {ω : Configuration d | ¬ ∀ x : Vertex d,
    ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)} with hN₀
  have hN₀0 : μ N₀ = 0 := ae_iff.1 hae
  set E : ℕ → Vertex d → Set (Configuration d) := fun k y =>
    {ω | (∃ z ∈ enl 1 k y, k < stoppingScale (G ω) z) ∨
      K * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ stoppingScale (G ω) x) ^ τ} with hE
  -- the deterministic step: off `N₀` and the events `E k x`, the Meyers estimate holds
  have hdet : ∀ ω (k : ℕ) (x : Vertex d), ω ∉ N₀ → ω ∉ E k x → MeyersCube ε CM ω k x := by
    intro ω k x hω hωE U₀ hU hcl u hu
    have hu' : ∀ x : Vertex d, ∃! Q : TriadicCube d, x ∈ Q.vertices ∧
        Q.IsMaximalStopping (G ω) := by
      by_contra h
      exact hω h
    simp only [hE, Set.mem_setOf_eq, not_or, not_exists, not_and, not_lt] at hωE
    obtain ⟨hsmall, hmom⟩ := hωE
    refine hMK ω U₀ u k x (fun z => stoppingScale (G ω) z) (fun a ha b hab hb => hcl a ha b hab hb)
      (fun a ha _ hall => hu a ha hall) (fun x' z hz => stoppingScale_eq_of_mem_cube hu' hz)
      (fun x' y hxy => stoppingScale_le_of_supDist hu' hxy) (fun z hz => ?_)
      (fun k' y hk' _ => mem_of_stoppingScale_le hu' hk') ?_
    · exact (cube_mono (hsmall z hz) z).trans (cube_subset_enl_of_mem hz)
    · refine le_trans (Finset.sum_le_sum fun x' _ => ?_) hmom
      calc ((3 : ℝ) ^ stoppingScale (G ω) x') ^ t
          ≤ ((3 : ℝ) ^ stoppingScale (G ω) x') ^ (τ : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)) htτ
        _ = ((3 : ℝ) ^ stoppingScale (G ω) x') ^ τ := Real.rpow_natCast _ τ
  rcases Nat.eq_zero_or_eq_succ_pred T.scale with h0 | hsucc
  · have hempty : {ω : Configuration d | T ∉ meyersGood ε CM ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not, meyersGood]
      intro k hk
      omega
    rw [hempty, measure_empty]
    exact zero_le
  · set k := T.scale.pred with hk
    have hTk : T.scale = k + 1 := hsucc
    have hTY : ∀ x, x ∈ T.vertices ↔ x ∈ cube T.scale T.center := by
      intro x
      have h := mem_triadicCube_idx_iff (k := T.scale) (z := T.center) (x := x)
      rwa [← triadicCube_eq_idx_center' T] at h
    have hsub : {ω : Configuration d | T ∉ meyersGood ε CM ω} ⊆
        N₀ ∪ ⋃ x ∈ cube T.scale T.center, E k x := by
      intro ω hω
      by_contra hn
      simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hn
      obtain ⟨hn0, hn1⟩ := hn
      apply hω
      intro k' hk' x hx
      have hkk : k' = k := by omega
      rw [hkk]
      exact hdet ω k x hn0 (hn1 x ((hTY x).1 hx))
    have hunion : μ (⋃ x ∈ cube T.scale T.center, E k x) ≤
        ENNReal.ofReal (((3 : ℝ) ^ (k + 1)) ^ d * (C2 * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r))) := by
      calc μ (⋃ x ∈ cube T.scale T.center, E k x)
          ≤ ∑ x ∈ cube T.scale T.center, μ (E k x) := measure_biUnion_finset_le _ _
        _ ≤ ∑ _x ∈ cube T.scale T.center,
              ENNReal.ofReal (C2 * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r)) :=
            Finset.sum_le_sum fun x _ => htail k x
        _ = _ := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_cube, hTk]
    have hexp : ((3 : ℝ) ^ (k + 1)) ^ d * (C2 * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r)) ≤
        K3 * C2 * Real.exp (-(c2 / 2 / 3 ^ r) * ((3 : ℝ) ^ T.scale) ^ r) := by
      have h1 := mul_le_mul_of_nonneg_left (hK3k k) hC2
      have e1 : ((3 : ℝ) ^ T.scale) ^ r = 3 ^ r * ((3 : ℝ) ^ k) ^ r := by
        rw [hTk, pow_succ, Real.mul_rpow (by positivity) (by norm_num), mul_comm]
      have e2 : -(c2 / 2 / 3 ^ r) * ((3 : ℝ) ^ T.scale) ^ r = -(c2 / 2) * ((3 : ℝ) ^ k) ^ r := by
        rw [e1]
        have : (0 : ℝ) < 3 ^ r := by positivity
        field_simp
      rw [e2]
      calc ((3 : ℝ) ^ (k + 1)) ^ d * (C2 * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r))
          = C2 * (((3 : ℝ) ^ (k + 1)) ^ d * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r)) := by ring
        _ ≤ C2 * (K3 * Real.exp (-(c2 / 2) * ((3 : ℝ) ^ k) ^ r)) := h1
        _ = _ := by ring
    calc μ {ω : Configuration d | T ∉ meyersGood ε CM ω}
        ≤ μ (N₀ ∪ ⋃ x ∈ cube T.scale T.center, E k x) := measure_mono hsub
      _ ≤ μ N₀ + μ (⋃ x ∈ cube T.scale T.center, E k x) := measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal (((3 : ℝ) ^ (k + 1)) ^ d *
            (C2 * Real.exp (-c2 * ((3 : ℝ) ^ k) ^ r))) := by
          rw [hN₀0]
          exact add_le_add le_rfl hunion
      _ ≤ _ := by
          rw [zero_add]
          exact ENNReal.ofReal_le_ofReal hexp

end FailureBound

/-- **The partition `𝓠_a` of Definition 3.9 with its minimal scales** (Armstrong and Dario,
Definition 3.9 with Propositions 2.1 and 2.4, in every dimension): for an exponent `ε > 0` and a
constant `C`, a cell scale `s` whose cells `cube (s x) x` form a partition with comparable
neighbours, whose predecessors are in the local family of the cubes with the Meyers estimate, and
whose minimal scales have stretched-exponential tails (the bound (3.21),
`𝓜_t(𝓠_a) = 𝒪_r(C)`). -/
def MeyersPartition (d : ℕ) (p : unitInterval) : Prop :=
  ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∃ s : Configuration d → Vertex d → ℕ,
    (∀ᵐ ω ∂(latticeBondLaw d p),
      (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex d), s ω y ≤ k →
        (⟨k, idx k y⟩ : TriadicCube d) ∈ meyersGood ε C ω) ∧
    ∀ t : ℝ, 0 < t → ∃ K : ℝ, 0 ≤ K ∧ ∃ C' c' r : ℝ, 0 ≤ C' ∧ 0 < c' ∧ 0 < r ∧
      ∀ (k : ℕ) (y : Vertex d),
      latticeBondLaw d p {ω | (∃ z ∈ enl 1 k y, k < s ω z) ∨
          K * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ s ω x) ^ t} ≤
        ENNReal.ofReal (C' * Real.exp (-c' * ((3 : ℝ) ^ k) ^ r))

/-- **The partition `𝓠_a` of Definition 3.9 of Armstrong and Dario with its minimal scales**, in
every dimension `d ≥ 2`, for supercritical bond percolation. -/
theorem meyersPartition_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) : MeyersPartition d p := by
  have hd0 : 0 < d := by omega
  obtain ⟨ε, C, hε, hC, C1, c, s0, hC1, hc, hs0, hs1, hfail⟩ := exists_meyersFailureBound hd hpc
  set G : Configuration d → Set (TriadicCube d) := meyersGood ε C with hG
  have hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω} := measurableSet_mem_meyersGood ε C
  have hloc := measurableSet_not_mem_meyersGood_local (d := d) ε C
  obtain ⟨hae, -, -⟩ := partition_estimates_general hd0 (latticeBondLaw d p) G hGm hC1 hc hs0 hfail
  refine ⟨ε, C, hε, hC, fun ω => stoppingScale (G ω), ?_, fun t ht => ?_⟩
  · filter_upwards [hae] with ω hu
    exact ⟨fun x z hz => stoppingScale_eq_of_mem_cube hu hz,
      fun x y hxy => stoppingScale_le_of_supDist hu hxy,
      fun k y hk => mem_of_stoppingScale_le hu hk⟩
  set τ : ℕ := ⌈t⌉₊ with hτ
  have htτ : t ≤ τ := Nat.le_ceil t
  obtain ⟨K, hK, C2, c2, r, hC2, hc2, hr0, -, htail⟩ :=
    exists_measure_stoppingScale_large_le hd0 p G hGm hloc hC1 hc hs0 hs1 hfail τ
  refine ⟨K, hK, C2, c2, r, hC2, hc2, hr0, fun k y => (measure_mono ?_).trans (htail k y)⟩
  intro ω hω
  rcases hω with h | h
  · exact Or.inl h
  · refine Or.inr (lt_of_lt_of_le h (Finset.sum_le_sum fun x _ => ?_))
    calc ((3 : ℝ) ^ stoppingScale (G ω) x) ^ t
        ≤ ((3 : ℝ) ^ stoppingScale (G ω) x) ^ (τ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)) htτ
      _ = ((3 : ℝ) ^ stoppingScale (G ω) x) ^ τ := Real.rpow_natCast _ τ

end Rigidity.Proofs.Cluster.GeneralDim
