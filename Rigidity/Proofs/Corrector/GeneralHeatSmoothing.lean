import Rigidity.Proofs.Corrector.GeneralPoincareMoments
import Rigidity.Proofs.Poincare.GeneralMultiscalePoincare
import Rigidity.Proofs.Poincare.GeneralHeatGradient

/-!
# Heat-kernel averages of the gradient of the coarsened corrector in every dimension

Dario's Step 1 of the proof of Theorem 2 uses `|Φ_{r²} * ∇[χ]_𝒫(x)|`, with `Φ` the heat kernel of
`ℤᵈ` (`Rigidity.Poincare.GeneralDim.zdHeat`, of mass one) and
`heatGradient u r x = Σ_j |Σ_y Φ(r², x, y) (u(y + e_j) - u(y))|`
(`Rigidity.Poincare.GeneralDim.heatGradient`). Here, for the coarsened correctors of the partition
into good cubes of `ℤᵈ`:

* `heatGradient_coarseField_isOsBond`: for every `r` and `x`,
  `|Φ_{r²} * ∇[χ]_𝒫(x)| ≤ O_s(C)` with `s, C` independent of `r, x` — the bound used by Dario for
  `r ≤ 1`, from the bound of the coarse gradients by the sums of (5.10)
  (`ofReal_abs_coarseField_step_le`) and the mass one of `Φ`;
* `ae_summable_heat_coarseField`: almost surely these convolutions converge absolutely, for
  every point, direction and radius;
* `darioOptimalCorrectorThree_of_prop31`: Dario's Theorem 1 in dimension `d ≥ 3` from his
  Proposition 3.1 (`DarioPropThreeOneThree`), with the multiscale Poincaré inequality (2.26) on
  `ℤᵈ` (`Rigidity.Poincare.GeneralDim.multiscalePoincare_holds`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim Rigidity.Proofs.S2
open scoped Classical ENNReal

variable {d : ℕ} {p : unitInterval}

theorem measurable_heatGradient [NeZero d] {F : Vertex d → Configuration d → ℝ}
    (hF : ∀ z, Measurable (F z)) (x : Vertex d) :
    Measurable fun rω : ℝ × Configuration d =>
      Rigidity.Poincare.GeneralDim.heatGradient (fun z => F z rω.2) rω.1 x := by
  unfold Rigidity.Poincare.GeneralDim.heatGradient
  refine Finset.measurable_sum _ fun j _ => (Measurable.tsum fun y => ?_).abs
  exact (((continuous_zdHeat x y).measurable.comp (measurable_fst.pow_const 2))).mul
    (((hF _).sub (hF y)).comp measurable_snd)

theorem measurable_heatGradient_const [NeZero d] {F : Vertex d → Configuration d → ℝ}
    (hF : ∀ z, Measurable (F z)) (r : ℝ) (x : Vertex d) :
    Measurable fun ω => Rigidity.Poincare.GeneralDim.heatGradient (fun z => F z ω) r x :=
  (measurable_heatGradient hF x).comp (f := fun ω => (r, ω)) (measurable_const.prodMk measurable_id)

theorem heatGradient_nonneg' (u : Vertex d → ℝ) (r : ℝ) (x : Vertex d) :
    0 ≤ Rigidity.Poincare.GeneralDim.heatGradient u r x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem ofReal_abs_tsum_le {ι : Type*} (f : ι → ℝ) :
    ENNReal.ofReal |∑' i, f i| ≤ ∑' i, ENNReal.ofReal |f i| := by
  by_cases hs : Summable f
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _) hs.abs]
    exact ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hs.norm)
  · rw [tsum_eq_zero_of_not_summable hs, abs_zero, ENNReal.ofReal_zero]
    positivity

theorem two_rpow_sub_one_mul_two {q : ℝ} (hq : 1 ≤ q) :
    (2 : ℝ≥0∞) ^ (q - 1) * 2 = 2 ^ q := by
  have h : ∀ t : ℝ, 0 ≤ t → (2 : ℝ≥0∞) ^ t = ENNReal.ofReal (2 ^ t) := fun t ht => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) ht, ENNReal.ofReal_ofNat]
  rw [h _ (by linarith), h _ (by linarith), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by positivity), Real.rpow_sub_one (by norm_num),
    div_mul_cancel₀ _ (by norm_num)]

/-- The moments of the heat-kernel averages of the sums of two neighbouring nonnegative variables
with uniform moments, for probability weights `w`. -/
theorem lintegral_heatSum_rpow_le [NeZero d] {w : Vertex d → ℝ≥0∞} (hw1 : ∑' y, w y = 1)
    {σ : Vertex d → Configuration d → ℝ≥0∞} (hσm : ∀ y, Measurable (σ y)) {A k q : ℝ}
    (hq : 1 ≤ q) (hA : 0 ≤ A)
    (hmom : ∀ y, ∫⁻ ω, σ y ω ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) :
    ∫⁻ ω, (∑ j : Fin d, ∑' y, w y * (σ (y + LatticeProb.unit j) ω + σ y ω)) ^ q
        ∂latticeBondLaw d p ≤ ENNReal.ofReal ((2 * d * A * q ^ k) ^ q) := by
  have hq0 : 0 < q := by linarith
  set g : Fin d → Vertex d → Configuration d → ℝ≥0∞ := fun j y ω =>
    σ (y + LatticeProb.unit j) ω + σ y ω with hg
  have hgm : ∀ j y, Measurable (g j y) := fun j y => (hσm _).add (hσm _)
  have hgmom : ∀ j y, ∫⁻ ω, g j y ω ^ q ∂latticeBondLaw d p ≤
      2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) := by
    intro j y
    calc ∫⁻ ω, g j y ω ^ q ∂latticeBondLaw d p
        ≤ ∫⁻ ω, 2 ^ (q - 1) * (σ (y + LatticeProb.unit j) ω ^ q + σ y ω ^ q)
            ∂latticeBondLaw d p :=
          lintegral_mono fun ω => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
      _ = 2 ^ (q - 1) * (∫⁻ ω, σ (y + LatticeProb.unit j) ω ^ q ∂latticeBondLaw d p +
            ∫⁻ ω, σ y ω ^ q ∂latticeBondLaw d p) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
            ENNReal.ofNat_ne_top), lintegral_add_left ((hσm _).pow_const q)]
      _ ≤ 2 ^ (q - 1) * (ENNReal.ofReal ((A * q ^ k) ^ q) + ENNReal.ofReal ((A * q ^ k) ^ q)) :=
          mul_le_mul_right (add_le_add (hmom _) (hmom _)) _
      _ = 2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) := by
          rw [← two_mul, ← mul_assoc, two_rpow_sub_one_mul_two hq]
  have hJ : ∀ j ω, (∑' y, w y * g j y ω) ^ q ≤ ∑' y, w y * g j y ω ^ q := by
    intro j ω
    have h := lintegral_mul_rpow_le (μ := Measure.count) (g := fun y => g j y ω) (w := w)
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
      (fun y => ne_top_of_le_ne_top ENNReal.one_ne_top (hw1 ▸ ENNReal.le_tsum y)) hq
    simp only [lintegral_count, hw1, ENNReal.one_rpow, mul_one] at h
    calc (∑' y, w y * g j y ω) ^ q = (∑' y, g j y ω * w y) ^ q := by
          simp_rw [mul_comm (w _)]
      _ ≤ ∑' y, g j y ω ^ q * w y := h
      _ = ∑' y, w y * g j y ω ^ q := by simp_rw [mul_comm (g _ _ _ ^ q)]
  have hTj : ∀ j, ∫⁻ ω, (∑' y, w y * g j y ω) ^ q ∂latticeBondLaw d p ≤
      2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) := by
    intro j
    calc ∫⁻ ω, (∑' y, w y * g j y ω) ^ q ∂latticeBondLaw d p
        ≤ ∫⁻ ω, ∑' y, w y * g j y ω ^ q ∂latticeBondLaw d p := lintegral_mono (hJ j)
      _ = ∑' y, w y * ∫⁻ ω, g j y ω ^ q ∂latticeBondLaw d p := by
          rw [lintegral_tsum fun y => (((hgm j y).pow_const q).const_mul _).aemeasurable]
          exact tsum_congr fun y => lintegral_const_mul' _ _
            (ne_top_of_le_ne_top ENNReal.one_ne_top (hw1 ▸ ENNReal.le_tsum y))
      _ ≤ ∑' y, w y * (2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q)) :=
          ENNReal.tsum_le_tsum fun y => mul_le_mul_right (hgmom j y) _
      _ = 2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) := by
          rw [ENNReal.tsum_mul_right, hw1, one_mul]
  set T : Fin d → Configuration d → ℝ≥0∞ := fun j ω => ∑' y, w y * g j y ω with hT
  have hTm : ∀ j, Measurable (T j) := fun j => Measurable.tsum fun y => (hgm j y).const_mul _
  have hsplit : ∀ ω, (∑ j : Fin d, T j ω) ^ q ≤
      (∑ j : Fin d, T j ω ^ q) * (d : ℝ≥0∞) ^ (q - 1) := by
    intro ω
    have h := lintegral_mul_rpow_le (μ := Measure.count) (g := fun j : Fin d => T j ω)
      (w := fun _ => 1) (measurable_of_countable _).aemeasurable aemeasurable_const
      (fun _ => ENNReal.one_ne_top) hq
    simpa [lintegral_count, tsum_fintype] using h
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hcast : (d : ℝ≥0∞) = ENNReal.ofReal d := (ENNReal.ofReal_natCast d).symm
  have h2 : (2 : ℝ≥0∞) ^ q = ENNReal.ofReal (2 ^ q) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq0.le, ENNReal.ofReal_ofNat]
  calc ∫⁻ ω, (∑ j : Fin d, T j ω) ^ q ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (∑ j : Fin d, T j ω ^ q) * (d : ℝ≥0∞) ^ (q - 1) ∂latticeBondLaw d p :=
        lintegral_mono hsplit
    _ = (∑ j : Fin d, ∫⁻ ω, T j ω ^ q ∂latticeBondLaw d p) * (d : ℝ≥0∞) ^ (q - 1) := by
        rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          (ENNReal.natCast_ne_top d)),
          lintegral_finsetSum _ fun j _ => (hTm j).pow_const q]
    _ ≤ (∑ _j : Fin d, 2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q)) * (d : ℝ≥0∞) ^ (q - 1) :=
        mul_le_mul_left (Finset.sum_le_sum fun j _ => hTj j) _
    _ = ENNReal.ofReal ((2 * d * A * q ^ k) ^ q) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcast,
          ENNReal.ofReal_rpow_of_nonneg hd0.le (by linarith), h2,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have e1 : (2 * (d : ℝ) * A * q ^ k) ^ q = 2 ^ q * (d : ℝ) ^ q * (A * q ^ k) ^ q := by
          rw [show 2 * (d : ℝ) * A * q ^ k = (2 * d) * (A * q ^ k) by ring,
            Real.mul_rpow (x := 2 * (d : ℝ)) (by positivity) (by positivity),
            Real.mul_rpow (x := 2) (y := (d : ℝ)) (by norm_num) hd0.le]
        have e2 : (d : ℝ) ^ q = (d : ℝ) ^ (q - 1) * d := by
          rw [← Real.rpow_add_one hd0.ne', sub_add_cancel]
        rw [e1, e2]
        ring

/-- A nonnegative variable dominated almost surely by a variable with moments `(A q^k)^q`
satisfies the moment hypothesis of `isOsBond_of_moment_le`, hence is `O_s(C)`. -/
theorem isOsBond_of_ae_ofReal_le {A k s C : ℝ} (hA : 0 ≤ A)
    (hmom : ∀ X : Configuration d → ℝ, Measurable X → (∀ ω, 0 ≤ X ω) →
      (∀ q : ℝ, 1 ≤ q → Integrable (fun ω => X ω ^ q) (latticeBondLaw d p) ∧
        ∫ ω, X ω ^ q ∂latticeBondLaw d p ≤ (A * q ^ k) ^ q) → IsOsBond d p X s C)
    {E : Configuration d → ℝ} (hEm : Measurable E) (hE0 : ∀ ω, 0 ≤ E ω)
    {T : Configuration d → ℝ≥0∞} (hpt : ∀ᵐ ω ∂latticeBondLaw d p, ENNReal.ofReal (E ω) ≤ T ω)
    (hT : ∀ q : ℝ, 1 ≤ q → ∫⁻ ω, T ω ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((A * q ^ k) ^ q)) :
    IsOsBond d p E s C := by
  refine hmom E hEm hE0 fun q hq => ?_
  have hq0 : 0 < q := by linarith
  have hmq : Measurable fun ω => E ω ^ q := hEm.pow_const q
  have hnn : 0 ≤ᵐ[latticeBondLaw d p] fun ω => E ω ^ q :=
    Eventually.of_forall fun ω => Real.rpow_nonneg (hE0 ω) q
  have hlin : ∫⁻ ω, ENNReal.ofReal (E ω ^ q) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((A * q ^ k) ^ q) := by
    refine (lintegral_mono_ae ?_).trans (hT q hq)
    filter_upwards [hpt] with ω hω
    rw [← ENNReal.ofReal_rpow_of_nonneg (hE0 ω) hq0.le]
    exact ENNReal.rpow_le_rpow hω hq0.le
  refine ⟨⟨hmq.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmq.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

section Carrier

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The gradient of the coarsened corrector along a lattice edge is at most the sums of (5.10) at
its endpoints. -/
theorem ofReal_abs_coarseField_step_le (hd : 0 < d) {ω : Configuration d} (hω : ω ∈ G)
    (hP : PartitionEvent ω) {i : Fin d} {Λ : Vertex d → Configuration d → ℝ}
    (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) (y : Vertex d) (j : Fin d) :
    ENNReal.ofReal
        |coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω| ≤
      stepSixSum Λ (y + LatticeProb.unit j) ω + stepSixSum Λ y ω := by
  have hinf : ∀ v, ω ∈ infiniteComponentEvent (partitionAnchor ω v) :=
    infinite_partitionAnchor hd hP
  have hA0 : ∀ v, shiftedAnchor 0 ω v = partitionAnchor ω v := fun v => by
    rw [shiftedAnchor_zero, guardAnchor_of_event hP]
  set w : Vertex d → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv (Pi.single i 1) ω x (partitionAnchor ω 0) else 0 with hw
  have hW : ∀ u, coarseField hG hGv i 0 u ω = w (partitionAnchor ω u) := by
    intro u
    simp only [hw, coarseField, hA0]
    rw [if_pos (hinf u)]
  rw [hW, hW]
  set y' := y + LatticeProb.unit j with hy'
  set S := anchorBox ω y' ∪ anchorBox ω y with hS
  have hadj : (nearestNeighborGraph d).Adj y' y := by
    change ∃ k : Fin d, y = y' + LatticeProb.unit k ∨ y' = y + LatticeProb.unit k
    exact ⟨j, Or.inr rfl⟩
  have hreach : (openIn ω ↑S).Reachable (partitionAnchor ω y') (partitionAnchor ω y) := by
    refine Rigidity.Percolation.openIn_reachable_mono_region ?_
      (reachable_partitionAnchor_of_adj hd hP hadj)
    rintro x (hx | hx)
    · exact Finset.mem_coe.2 (Finset.mem_union_left _ (mem_anchorBox_of_mem_partitionCube hP hx))
    · exact Finset.mem_coe.2 (Finset.mem_union_right _ (mem_anchorBox_of_mem_partitionCube hP hx))
  have hv := abs_sub_le_edgeVariationIn_of_reachable S w hreach
  have hev := edgeVariationIn_correctorDiff_le hG hGv hω (hinf 0) S (Λ := fun x => Λ x ω) hΛ0 hΛ
  have hun : ∑ x ∈ S, Λ x ω ≤ ∑ x ∈ anchorBox ω y', Λ x ω + ∑ x ∈ anchorBox ω y, Λ x ω := by
    have h := Finset.sum_union_inter (s₁ := anchorBox ω y') (s₂ := anchorBox ω y)
      (f := fun x => Λ x ω)
    have h0 : 0 ≤ ∑ x ∈ anchorBox ω y' ∩ anchorBox ω y, Λ x ω :=
      Finset.sum_nonneg fun x _ => hΛ0 x
    linarith
  calc ENNReal.ofReal |w (partitionAnchor ω y') - w (partitionAnchor ω y)|
      ≤ ENNReal.ofReal (2 * d * ∑ x ∈ anchorBox ω y', Λ x ω +
          2 * d * ∑ x ∈ anchorBox ω y, Λ x ω) := by
        refine ENNReal.ofReal_le_ofReal (hv.trans (hev.trans ?_))
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left hun (by positivity)
    _ ≤ ENNReal.ofReal (2 * d * ∑ x ∈ anchorBox ω y', Λ x ω) +
          ENNReal.ofReal (2 * d * ∑ x ∈ anchorBox ω y, Λ x ω) := ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add (ofReal_sum_anchorBox_le hP hΛ0 y') (ofReal_sum_anchorBox_le hP hΛ0 y)

/-- The heat-kernel average of the gradient of the coarsened corrector is at most the heat-kernel
average of the sums of (5.10) at the endpoints of the edges. -/
theorem ofReal_heatGradient_le [NeZero d] {ω : Configuration d} (hω : ω ∈ G)
    (hP : PartitionEvent ω) {i : Fin d} {Λ : Vertex d → Configuration d → ℝ}
    (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) (r : ℝ) (x : Vertex d) :
    ENNReal.ofReal
        (Rigidity.Poincare.GeneralDim.heatGradient (fun z => coarseField hG hGv i 0 z ω) r x) ≤
      ∑ j : Fin d, ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y) *
        (stepSixSum Λ (y + LatticeProb.unit j) ω + stepSixSum Λ y ω) := by
  unfold Rigidity.Poincare.GeneralDim.heatGradient
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
  refine Finset.sum_le_sum fun j _ => (ofReal_abs_tsum_le _).trans
    (ENNReal.tsum_le_tsum fun y => ?_)
  rw [abs_mul, abs_of_nonneg (zdHeat_nonneg (sq_nonneg r) x y),
    ENNReal.ofReal_mul (zdHeat_nonneg (sq_nonneg r) x y)]
  exact mul_le_mul_right (ofReal_abs_coarseField_step_le hG hGv (Nat.pos_of_neZero d) hω hP hΛ0
    hΛ y j) _

/-- **The heat-kernel averages of the gradient of the coarsened corrector are `O_s(C)`**,
uniformly in the radius and the point (the bound used by Dario for `r ≤ 1`). -/
theorem heatGradient_coarseField_isOsBond [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (i : Fin d) (r : ℝ) (x : Vertex d),
      IsOsBond d p
        (fun ω => Rigidity.Poincare.GeneralDim.heatGradient
          (fun z => coarseField hG hGv i 0 z ω) r x) s C := by
  obtain ⟨Λ, A, k, hA0, hk0, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hd hpc hp1 hGae
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs0 : 0 < 1 / (2 * k) := by positivity
  have hsk : 1 / (2 * k) * k < 1 := by field_simp; linarith
  obtain ⟨C, hC, hmom⟩ := isOsBond_of_moment_le (d := d) (p := p)
    (by positivity : 0 < 2 * d * A) hs0 hsk
  refine ⟨1 / (2 * k), C, hs0, hC, fun i r x => ?_⟩
  have hEm := measurable_heatGradient_const (fun z => measurable_coarseField hG hGv i 0 z) r x
  have hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  have hpt : ∀ᵐ ω ∂latticeBondLaw d p,
      ENNReal.ofReal
          (Rigidity.Poincare.GeneralDim.heatGradient (fun z => coarseField hG hGv i 0 z ω) r x) ≤
        ∑ j : Fin d, ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y) *
          (stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω) := by
    filter_upwards [hGae, ae_partitionEvent hd hpc, hall] with ω hω hP hl
    exact ofReal_heatGradient_le hG hGv hω hP (fun x => hΛ0 i x ω) hl r x
  have hmom' : ∀ X : Configuration d → ℝ, Measurable X → (∀ ω, 0 ≤ X ω) →
      (∀ q : ℝ, 1 ≤ q → Integrable (fun ω => X ω ^ q) (latticeBondLaw d p) ∧
        ∫ ω, X ω ^ q ∂latticeBondLaw d p ≤ (2 * d * A * q ^ k) ^ q) → IsOsBond d p X _ C :=
    hmom
  exact isOsBond_of_ae_ofReal_le (A := 2 * d * A) (by positivity) hmom' hEm
    (fun ω => heatGradient_nonneg' _ _ _) hpt
    fun q hq => lintegral_heatSum_rpow_le (tsum_ofReal_zdHeat (sq_nonneg r) x)
      (fun y => measurable_stepSixSum (hΛm i) y) hq hA0.le (fun y => hmom6 i y q hq)

/-- **The heat-kernel averages of the gradient of the coarsened corrector converge**: almost
surely, for every point, direction and radius, `Σ_y Φ(r², x, y) ∇_j[χ]_𝒫(y)` converges
absolutely, since `Φ(r², x, ·) ≤ e^{4dT} Φ(2T, x, ·)` for `r² ≤ T` and the sums of (5.10) have
bounded means. -/
theorem ae_summable_heat_coarseField [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (i : Fin d) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (x : Vertex d) (j : Fin d) (r : ℝ), 0 < r →
      Summable fun y => zdHeat d (r ^ 2) x y *
        (coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω) := by
  obtain ⟨Λ, A, k, -, -, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hd hpc hp1 hGae
  have hgm : ∀ (j : Fin d) (y : Vertex d), Measurable fun ω =>
      stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω := fun j y =>
    (measurable_stepSixSum (hΛm i) _).add (measurable_stepSixSum (hΛm i) _)
  have h1 : ∀ v, ∫⁻ ω, stepSixSum (Λ i) v ω ∂latticeBondLaw d p ≤ ENNReal.ofReal A := by
    intro v
    have := hmom6 i v 1 le_rfl
    simpa only [ENNReal.rpow_one, Real.one_rpow, mul_one, Real.rpow_one] using this
  have hfin : ∀ (x : Vertex d) (j : Fin d) (T : ℕ), ∀ᵐ ω ∂latticeBondLaw d p,
      ∑' y, ENNReal.ofReal (zdHeat d (2 * T) x y) *
        (stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω) < ∞ := by
    intro x j T
    refine ae_lt_top (Measurable.tsum fun y => (hgm j y).const_mul _) ?_
    rw [lintegral_tsum fun y => ((hgm j y).const_mul _).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' y : Vertex d,
      ENNReal.ofReal (zdHeat d (2 * T) x y) * (2 * ENNReal.ofReal A)) ?_ ?_
    · rw [ENNReal.tsum_mul_right, tsum_ofReal_zdHeat (by positivity) x, one_mul]
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun y => ?_
      rw [lintegral_const_mul _ (hgm j y),
        lintegral_add_left (measurable_stepSixSum (hΛm i) _)]
      exact mul_le_mul_right (by rw [two_mul]; exact add_le_add (h1 _) (h1 _)) _
  have hfin' : ∀ᵐ ω ∂latticeBondLaw d p, ∀ (x : Vertex d) (j : Fin d) (T : ℕ),
      ∑' y, ENNReal.ofReal (zdHeat d (2 * T) x y) *
        (stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω) < ∞ :=
    ae_all_iff.2 fun x => ae_all_iff.2 fun j => ae_all_iff.2 fun T => hfin x j T
  have hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  filter_upwards [hGae, ae_partitionEvent hd hpc, hall, hfin'] with ω hω hP hl hf x j r hr
  set T : ℕ := ⌈r ^ 2⌉₊ with hT
  have hrT : r ^ 2 ≤ T := Nat.le_ceil _
  have hT0 : (0 : ℝ) ≤ 2 * T := by positivity
  have hs : Summable fun y => zdHeat d (2 * T) x y *
      |coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω| := by
    refine (ENNReal.summable_toReal (ne_top_of_le_ne_top (hf x j T).ne
      (ENNReal.tsum_le_tsum fun y => ?_))).congr fun y => ENNReal.toReal_ofReal
        (mul_nonneg (zdHeat_nonneg hT0 x y) (abs_nonneg _))
    rw [ENNReal.ofReal_mul (zdHeat_nonneg hT0 x y)]
    exact mul_le_mul_right (ofReal_abs_coarseField_step_le hG hGv (by omega) hω hP
      (fun x => hΛ0 i x ω) hl y j) _
  refine summable_abs_iff.mp (Summable.of_nonneg_of_le (fun y => abs_nonneg _) (fun y => ?_)
    (hs.mul_left (Real.exp (4 * d * T))))
  rw [abs_mul, abs_of_nonneg (zdHeat_nonneg (sq_nonneg r) x y), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (zdHeat_le_exp_mul (sq_nonneg r) hrT x y) (abs_nonneg _)

end Carrier

/-- **Dario's Proposition 3.1 in dimension `d ≥ 3`** for the coarsened correctors (hypothesis):
`|Φ_{r²} * ∇[χ_{e_i}]_𝒫(x)| ≤ O_s(C r^{-d/2})` for `r ≥ 1`, on every measurable conull carrier
of the qualitative corrector input. -/
def DarioPropThreeOneThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (i : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
        IsOsBond d p
          (fun ω => Rigidity.Poincare.GeneralDim.heatGradient
            (fun z => coarseField hG hGv i 0 z ω) r x) s
          (C / r ^ ((d : ℝ) / 2))

/-- **Dario's Theorem 1 in dimension `d ≥ 3`** (`DarioOptimalCorrectorThree`) from his
Proposition 3.1 in dimension `d ≥ 3`; the multiscale Poincaré inequality (2.26) on `ℤᵈ`, the
Lipschitz bound of the smoothed gradients, the comparison (5.7) and the coarsening error (5.10)
are proved. -/
theorem darioOptimalCorrectorThree_of_prop31 (h31 : DarioPropThreeOneThree) :
    DarioOptimalCorrectorThree := by
  refine darioOptimalCorrectorThree_of_poincareInputs fun d _ hd3 p hpc hp1 G hG hGv hGae => ?_
  have hd : 2 ≤ d := by omega
  obtain ⟨A₀, hA₀, hMSP⟩ := multiscalePoincare_holds (d := d)
  obtain ⟨s₁, C₁, hs₁, hC₁, h1⟩ := h31 d hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨s₂, C₂, hs₂, hC₂, h2⟩ := heatGradient_coarseField_isOsBond hG hGv hd hpc hp1 hGae
  set s := min s₁ s₂
  have hs : 0 < s := lt_min hs₁ hs₂
  set C := max C₁ C₂ * 6 ^ (1 / s)
  have hC : 0 < C := mul_pos (lt_max_of_lt_left hC₁) (by positivity)
  refine ⟨fun i r x ω =>
      Rigidity.Poincare.GeneralDim.heatGradient (fun z => coarseField hG hGv i 0 z ω) r x,
    A₀, C, s, hA₀, hC, hs,
    fun i x => measurable_heatGradient (fun z => measurable_coarseField hG hGv i 0 z) x,
    fun i r x ω => heatGradient_nonneg' _ _ _,
    fun i m hm q hq => (ae_summable_heat_coarseField hG hGv hd hpc hp1 hGae i).mono fun ω hω =>
      hMSP (fun z => coarseField hG hGv i 0 z ω) hω m hm q hq,
    fun i r hr x => ?_, fun i r _ _ x => ?_⟩
  · have hm := measurable_heatGradient_const (fun z => measurable_coarseField hG hGv i 0 z) r x
    have := IsOsBond.mono_exponent hs (min_le_left _ _) hm (h1 i r hr x)
    have hr0 : 0 < r ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    refine IsOsBond.mono_scale hs (by have := div_pos hC₁ hr0; positivity) ?_ hm this
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) hr0.le
  · have hm := measurable_heatGradient_const (fun z => measurable_coarseField hG hGv i 0 z) r x
    have := IsOsBond.mono_exponent hs (min_le_right _ _) hm (h2 i r x)
    exact IsOsBond.mono_scale hs (by positivity) (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity)) hm this

end Rigidity.Corrector.GeneralDim
