import Rigidity.Proofs.Corrector.GeneralStepTwoFiniteWeight
import Rigidity.Proofs.Corrector.GeneralStepOneGrowth
import Rigidity.Proofs.Corrector.GeneralCoarseningError
import PercolationClusterHomogenization.Proofs.Partition.AlmostSure
import LatticeProb.Prob.Percolation.LatticeRadialTail

/-!
# The good events of the finite-range weight on `ℤᵈ` are likely

* `measure_not_farGood_le`: an edge with its tail `v` outside `B(u, R)` reaching `u` needs
  `|u - v| ≤ 3dκ σ(v)` (the Euclidean norm of a point of an `ℓ^∞` box of radius `r` is at most
  `d r`), so a union bound with the exponential tail of the sizes of the partition into good cubes
  (`partition_estimates`) gives `P(¬ FarGood) ≤ 2 (2 (1 + 2d · 3dκθ))ᵈ e^{-R/(2 · 3dκθ)}`;
* `measure_not_sideGood_le`: a difference between the side and the capped side at a vertex of
  `B(u, R)` is a discrepancy of the capped partition, of probability `(2R + 1)ᵈ C e^{-c 3ⁿ}`;
* `measure_not_gradGood_le`: a failure of the local gradient bound at a site of `B(u, R + 3κR)` is
  a failure of `LocalGradGood` for the configuration seen from the site, which has the law of the
  configuration; for `d ≥ 3` this has the tail of `measure_not_localGradGood_le`.

This ports the planar file `DarioStepTwoFiniteProb`: the planar partition becomes the partition
into good cubes of `ℤᵈ`, the factor `2` of the Euclidean radius of a planar box becomes `d`, the
lattice sum `Σ_v e^{-|v - u|/κ}` is bounded by `(2 (1 + dκ))ᵈ` (`tsum_exp_neg_norm_sub_le`), the
count `(2R + 1)²` of a box becomes `(2R + 1)ᵈ`, and the planar tail `C e^{-c √(R + 1)}` of the
finite clusters becomes `C e^{-c (R + 1)^{1/d}}`.

For the sides of the configurations with one bond `E (v, k)` closed at each tail `v`,
`measure_not_farGoodFlip_le` and `measure_not_sideGoodFlip_le` give the same bounds times
`d/(1 - p)` (`measure_preimage_setBond_false_le`), the partitions of all these configurations
existing almost surely (`ae_partitionEvent_setBond`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open Rigidity.Poincare.GeneralDim (supBox mem_supBox card_supBox)
open scoped Classical ENNReal

variable {d : ℕ}

theorem lt_norm_of_notMem_supBox {u v : Vertex d} {R : ℕ} (h : v ∉ supBox u R) :
    (R : ℝ) < ‖latticeEuclideanEmbedding (v - u)‖ := by
  rw [mem_supBox] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h1 := abs_coord_le_norm (v - u) i
  have h2 : (R : ℝ) < |(((v - u) i : ℤ) : ℝ)| := by
    simp only [Pi.sub_apply]
    exact_mod_cast hi
  linarith

/-- The far tail at one vertex: `v ∉ B(u, R)` and `|v - u| ≤ K σ(v)` has probability at most
`2 e^{-R/(2Kθ)} e^{-|v - u|/(2Kθ)}`, from the exponential moment of the size `σ(v)`. -/
theorem measure_far_le [NeZero d] {p : unitInterval} {θ K : ℝ} (hθ : 0 < θ) (hK : 0 < K)
    (hexp : ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        (latticeBondLaw d p) ∧
      ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ)
        ∂latticeBondLaw d p ≤ 2)
    (u v : Vertex d) (R : ℕ) :
    latticeBondLaw d p {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
      K * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(R / (2 * (K * θ))))) *
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * (K * θ)))) := by
  set c := K * θ with hc
  have hc0 : 0 < c := by positivity
  by_cases hvR : v ∈ supBox u R
  · have : {ω : Configuration d | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
        K * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} = ∅ := by
      ext ω; simp [hvR]
    rw [this, measure_empty]
    positivity
  · have hR := lt_norm_of_notMem_supBox hvR
    set t := ‖latticeEuclideanEmbedding (v - u)‖
    have hm := measure_le_mul_stoppingSize_le hθ hK v (hexp v).1 (hexp v).2 t
    refine (measure_mono fun ω hω => hω.2).trans (hm.trans ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (R : ℝ) / (2 * c) ≤ t / (2 * c) := div_le_div_of_nonneg_right hR.le (by positivity)
    have e : t / c = t / (2 * c) + t / (2 * c) := by field_simp; ring
    have key : -(t / c) ≤ -(R / (2 * c)) + -t / (2 * c) := by
      rw [e, neg_div]; linarith
    calc 2 * Real.exp (-(t / c)) ≤ 2 * Real.exp (-(R / (2 * c)) + -t / (2 * c)) := by
          gcongr
      _ = 2 * Real.exp (-(R / (2 * c))) * Real.exp (-t / (2 * c)) := by
          rw [Real.exp_add]; ring

/-- **Far edges do not reach `u`, with high probability.** -/
theorem measure_not_farGood_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (κ R : ℕ), 1 ≤ κ → ∀ u : Vertex d,
      latticeBondLaw d p {ω | PartitionEvent ω ∧ ¬ FarGood κ R ω u} ≤
        ENNReal.ofReal (2 * (2 * (1 + d * (2 * (3 * d * κ * θ)))) ^ d *
          Real.exp (-(R / (2 * (3 * d * κ * θ))))) := by
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  refine ⟨θ', hθ', fun κ R hκ u => ?_⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hK : (0 : ℝ) < 3 * d * κ := by positivity
  set c := 3 * (d : ℝ) * κ * θ' with hc
  have hc0 : 0 < c := by positivity
  have hsub : {ω | PartitionEvent ω ∧ ¬ FarGood κ R ω u} ⊆
      ⋃ v, {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
        3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} := by
    rintro ω ⟨hP, hfar⟩
    unfold FarGood at hfar
    push Not at hfar
    obtain ⟨v, hv, hvR⟩ := hfar
    refine Set.mem_iUnion.2 ⟨v, hvR, ?_⟩
    have h1 := norm_latticeEuclideanEmbedding_le_of_abs_le (z := u - v)
      (R := ((3 * κ * partSide ω v : ℕ) : ℝ)) (Nat.cast_nonneg _) fun i => by
        have h := (mem_supBox.1 hv) i
        rw [Pi.sub_apply]
        exact_mod_cast h
    rw [LatticeProb.Percolation.latticeEuclideanEmbedding_sub, norm_sub_rev,
        ← LatticeProb.Percolation.latticeEuclideanEmbedding_sub,
        stoppingSize_eq_partSide hP]
    push_cast at h1
    linarith
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
  have hv : ∀ v, latticeBondLaw d p {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
      3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(R / (2 * c)))) *
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * c))) :=
    fun v => measure_far_le hθ' hK hexp u v R
  refine (ENNReal.tsum_le_tsum hv).trans ?_
  rw [ENNReal.tsum_mul_left]
  have hs := tsum_exp_neg_norm_sub_le u (κ := 2 * c) (by positivity)
  calc ENNReal.ofReal (2 * Real.exp (-(R / (2 * c)))) *
        ∑' v, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * c)))
      ≤ ENNReal.ofReal (2 * Real.exp (-(R / (2 * c)))) *
        ENNReal.ofReal ((2 * (1 + d * (2 * c))) ^ d) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

theorem lt_three_mul_three_pow_capScale (R : ℕ) : R < 3 * 3 ^ capScale R := by
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) R
  rw [pow_succ] at this
  unfold capScale
  omega

/-- **The capped sides are the sides near `u`, with high probability.** -/
theorem measure_not_sideGood_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (R : ℕ) (u : Vertex d),
      latticeBondLaw d p {ω | PartitionEvent ω ∧ ¬ SideGood R ω u} ≤
        ((2 * R + 1) ^ d : ℕ) * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ capScale R))) := by
  obtain ⟨C, hC, c, hc, hD⟩ := measure_exists_cappedDiscrepancy_le hd hpc
  refine ⟨C, hC, c, hc, fun R u => (measure_mono ?_).trans (hD (capScale R) u R)⟩
  rintro ω ⟨hP, hs⟩
  unfold SideGood at hs
  push Not at hs
  obtain ⟨v, hv, hne⟩ := hs
  exact ⟨v, hv, not_not.1 fun hdisc => hne (partSide_eq_cappedSide hP hdisc)⟩

/-! ### The configurations with one bond closed -/

/-- **Far edges do not reach `u` for the sides with one bond closed, with high probability**: for
any bonds `E (v, k)`, the tail of the sizes of the partition of `ω^{E(v,k),0}` is that of `ω` up to
the factor `1/(1 - p)`, and the union over the `d` edges at each tail gives the factor `d`. -/
theorem measure_not_farGoodFlip_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (E : LatticeEdge d → Bond d) (κ R : ℕ), 1 ≤ κ → ∀ u : Vertex d,
      latticeBondLaw d p {ω | ¬ FarGoodFlip E κ R ω u} ≤
        ENNReal.ofReal (d * (2 * (2 * (1 + d * (2 * (3 * d * κ * θ)))) ^ d *
          Real.exp (-(R / (2 * (3 * d * κ * θ))))) / (1 - p)) := by
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  refine ⟨θ', hθ', fun E κ R hκ u => ?_⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hK : (0 : ℝ) < 3 * d * κ := by positivity
  have hq : (0 : ℝ) < 1 - p := by linarith
  set c := 3 * (d : ℝ) * κ * θ' with hc
  have hc0 : 0 < c := by positivity
  have hN0 : latticeBondLaw d p
      {ω | ¬ ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)} = 0 :=
    ae_iff.1 (ae_partitionEvent_setBond hd hpc hp1)
  have hSm : ∀ v, MeasurableSet {ω : Configuration d | v ∉ supBox u R ∧
      ‖latticeEuclideanEmbedding (v - u)‖ ≤
        3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} := fun v =>
    (MeasurableSet.const _).inter (measurableSet_le measurable_const
      ((measurable_stoppingSize_goodCubes v).const_mul _))
  have hsub : {ω | ¬ FarGoodFlip E κ R ω u} ⊆
      {ω | ¬ ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)} ∪
        ⋃ v, ⋃ k : Fin d, setBond (E (v, k)) false ⁻¹'
          {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
            3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    unfold FarGoodFlip at hω
    push Not at hω
    obtain ⟨v, k, hv, hvR⟩ := hω
    by_cases hP : ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)
    · right
      refine Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨k, hvR, ?_⟩⟩
      have h1 := norm_le_of_mem_supBox hv
      rw [LatticeProb.Percolation.latticeEuclideanEmbedding_sub, norm_sub_rev,
          ← LatticeProb.Percolation.latticeEuclideanEmbedding_sub,
          stoppingSize_eq_partSide (hP _ _)]
      push_cast at h1
      linarith
    · exact Or.inl hP
  have hv : ∀ v, latticeBondLaw d p {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
      3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(R / (2 * c)))) *
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * c))) :=
    fun v => measure_far_le hθ' hK hexp u v R
  have hterm : ∀ v, latticeBondLaw d p (⋃ k : Fin d, setBond (E (v, k)) false ⁻¹'
      {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
        3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v}) ≤
      (d * (ENNReal.ofReal (1 - p))⁻¹ * ENNReal.ofReal (2 * Real.exp (-(R / (2 * c))))) *
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * c))) := by
    intro v
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ k : Fin d, latticeBondLaw d p (setBond (E (v, k)) false ⁻¹'
          {ω | v ∉ supBox u R ∧ ‖latticeEuclideanEmbedding (v - u)‖ ≤
            3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v})
        ≤ ∑ _k : Fin d, (ENNReal.ofReal (1 - p))⁻¹ *
            (ENNReal.ofReal (2 * Real.exp (-(R / (2 * c)))) *
              ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * c)))) :=
          Finset.sum_le_sum fun k _ =>
            (measure_preimage_setBond_false_le hp1 (hSm v) _).trans (by gcongr; exact hv v)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ac_rfl
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hN0, zero_add]
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hterm).trans ?_)
  rw [ENNReal.tsum_mul_left]
  have hs := tsum_exp_neg_norm_sub_le u (κ := 2 * c) (by positivity)
  have hreal : 2 * Real.exp (-(R / (2 * c))) * (2 * (1 + d * (2 * c))) ^ d =
      2 * (2 * (1 + d * (2 * c))) ^ d * Real.exp (-(R / (2 * c))) := by ring
  calc (d * (ENNReal.ofReal (1 - p))⁻¹ * ENNReal.ofReal (2 * Real.exp (-(R / (2 * c))))) *
        ∑' v, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (v - u)‖ / (2 * c)))
      ≤ (d * (ENNReal.ofReal (1 - p))⁻¹ * ENNReal.ofReal (2 * Real.exp (-(R / (2 * c))))) *
        ENNReal.ofReal ((2 * (1 + d * (2 * c))) ^ d) := by gcongr
    _ = _ := by
        rw [mul_assoc (d * (ENNReal.ofReal (1 - p))⁻¹), ← ENNReal.ofReal_mul (by positivity),
          hreal, ENNReal.ofReal_div_of_pos hq, ENNReal.div_eq_inv_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        ac_rfl

/-- **The capped sides with one bond closed are their sides near `u`, with high probability.** -/
theorem measure_not_sideGoodFlip_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (E : LatticeEdge d → Bond d) (R : ℕ) (u : Vertex d),
        latticeBondLaw d p {ω | ¬ SideGoodFlip E R ω u} ≤
          ((d * (2 * R + 1) ^ d : ℕ) : ℝ≥0∞) *
            (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ capScale R) / (1 - p))) := by
  obtain ⟨C, hC, c, hc, hD⟩ := measure_exists_cappedDiscrepancy_setBond_le hd hpc hp1
  refine ⟨C, hC, c, hc, fun E R u => ?_⟩
  have hN0 : latticeBondLaw d p
      {ω | ¬ ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)} = 0 :=
    ae_iff.1 (ae_partitionEvent_setBond hd hpc hp1)
  have hsub : {ω | ¬ SideGoodFlip E R ω u} ⊆
      {ω | ¬ ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)} ∪
        {ω | ∃ v ∈ supBox u R, ∃ k : Fin d,
          CubeCappedDiscrepancy (setBond (E (v, k)) false ω) (capCube (capScale R) v)} := by
    intro ω hω
    by_cases hP : ∀ (e : Bond d) (b : Bool), PartitionEvent (setBond e b ω)
    · right
      simp only [Set.mem_setOf_eq] at hω
      unfold SideGoodFlip at hω
      push Not at hω
      obtain ⟨v, hv, k, hne⟩ := hω
      exact ⟨v, hv, k, not_not.1 fun hdisc => hne (partSide_eq_cappedSide (hP _ _) hdisc)⟩
    · exact Or.inl hP
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hN0, zero_add]
  exact hD E (capScale R) u R

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The local gradient bounds dominate the plane gradient bound near `u`, with high
probability**, for `d ≥ 3`. -/
theorem measure_not_gradGood_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ C₁ c₁ s δ C₂ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ 0 < s ∧ 0 < δ ∧ 0 < C₂ ∧ ∀ (κ R : ℕ) (i : Fin d),
      1 ≤ R → ∀ u : Vertex d,
        latticeBondLaw d p {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u} ≤
          ((2 * (R + 3 * κ * R) + 1) ^ d : ℕ) *
            ENNReal.ofReal ((2 * R + 1) ^ d *
                (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ (d : ℝ)⁻¹))) +
              2 * Real.exp (-((R : ℝ) / (C₂ * (2 * (d : ℝ) * R) ^ (1 - δ))) ^ s)) := by
  obtain ⟨C₁, c₁, s, δ, C₂, h1, h2, h3, h4, h5, hL⟩ :=
    measure_not_localGradGood_le hG hGv hd hpc hp1
  refine ⟨C₁, c₁, s, δ, C₂, h1, h2, h3, h4, h5, fun κ R i hR u => ?_⟩
  have hG0 : latticeBondLaw d p Gᶜ = 0 := ae_iff.1 hGae
  have hsub : {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u} ⊆
      ⋃ z ∈ supBox u (R + 3 * κ * R), (configurationTranslation (-z) ⁻¹' Gᶜ ∪
        configurationTranslation (-z) ⁻¹' {ω | ω ∈ G ∧ ¬ LocalGradGood hG hGv i R ω}) := by
    rintro ω ⟨hω, hg⟩
    unfold GradGood at hg
    push Not at hg
    obtain ⟨z, hz, hlt⟩ := hg
    refine Set.mem_iUnion₂.2 ⟨z, hz, ?_⟩
    by_cases hτ : configurationTranslation (-z) ω ∈ G
    · exact Or.inr ⟨hτ, fun hgood =>
        absurd (planeGrad_le_siteGrad hG hGv hω hR hτ hgood) (not_le.2 hlt)⟩
    · exact Or.inl hτ
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc _ ≤ ∑ _z ∈ supBox u (R + 3 * κ * R),
        ENNReal.ofReal ((2 * R + 1) ^ d *
            (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ (d : ℝ)⁻¹))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (2 * (d : ℝ) * R) ^ (1 - δ))) ^ s)) :=
        Finset.sum_le_sum fun z _ => by
          have hmp := measurePreserving_configurationTranslation p (-z)
          refine (measure_union_le _ _).trans
            ((add_le_add (hmp.measure_preimage_le _) (hmp.measure_preimage_le _)).trans ?_)
          rw [hG0, zero_add]
          exact hL i R hR
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_supBox]

end Grad

end Rigidity.Corrector.GeneralDim
