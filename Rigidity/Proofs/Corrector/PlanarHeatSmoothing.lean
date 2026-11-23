import Rigidity.Proofs.Corrector.PlanarDarioCorrector
import Rigidity.Proofs.Green.LazyHeatMass
import Rigidity.Proofs.Green.PlanarHeatKernelInputs
import Rigidity.Proofs.Green.LazyCarneVaropoulos
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Heat-kernel averages of the gradient of the coarsened corrector

Dario's Step 1 of the proof of Theorem 2 uses `|Φ_{r²} * ∇[χ]_𝒫(x)|`, with `Φ` the heat kernel of
`ℤ²` (Definition 2.18). Here `latticeHeat t x y` is the heat kernel of the variable speed random
walk on the lattice (the open graph of the configuration with every bond open), of mass one
(`tsum_ofReal_latticeHeat`), and `heatGradient u r x = Σ_j |Σ_y Φ(r², x, y) (u(y + e_j) - u(y))|`.

* `heatGradient_coarseField_isOsBond`: for every `r` and `x`,
  `|Φ_{r²} * ∇[χ]_𝒫(x)| ≤ O_s(C)` with `s, C` independent of `r, x` — the bound used by Dario for
  `r ≤ 1`, from the Lipschitz bound (2.22) of the coarsened corrector (here: main's coarse
  gradients and the sums of (5.10)) and the mass one of `Φ`;
* `ae_summable_heat_coarseField`: almost surely these convolutions converge absolutely, for
  every point, direction and radius;
* `darioOptimalCorrectorTwo_of_prop31`: Dario's Theorem 1 in dimension two from R2, R3, the
  multiscale Poincaré inequality (`MultiscalePoincareTwo`, Proposition 2.19 in cube form,
  deterministic) and Proposition 3.1 (`DarioPropThreeOneTwo`) for this `heatGradient`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.S2
open scoped Classical ENNReal

theorem ofReal_abs_tsum_le {ι : Type*} (f : ι → ℝ) :
    ENNReal.ofReal |∑' i, f i| ≤ ∑' i, ENNReal.ofReal |f i| := by
  by_cases hs : Summable f
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _) hs.abs]
    exact ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hs.norm)
  · rw [tsum_eq_zero_of_not_summable hs, abs_zero, ENNReal.ofReal_zero]
    positivity

/-- The heat kernel of `ℤ²` (Dario, Definition 2.18), as the heat kernel of the variable speed
random walk on the open graph of the configuration with every bond open. -/
noncomputable def latticeHeat (t : ℝ) (x y : Vertex 2) : ℝ :=
  Rigidity.Green.openHeat (allOpen 2) t x y

theorem latticeHeat_nonneg {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) : 0 ≤ latticeHeat t x y :=
  Rigidity.Green.openHeat_nonneg _ ht x y

theorem tsum_ofReal_latticeHeat {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    ∑' y, ENNReal.ofReal (latticeHeat t x y) = 1 :=
  Rigidity.Green.tsum_ofReal_vsrwHeat (by norm_num)
    (Rigidity.Green.openGraph_degree_le_four (allOpen 2)) ht x

theorem continuous_latticeHeat (x y : Vertex 2) : Continuous fun t => latticeHeat t x y :=
  Rigidity.Green.continuous_openHeat _ x y

/-- `Φ(t, x, y) ≤ 3 e^{T/18} e^{-|y - x|/18}` for `0 < t ≤ T`, from the bound of the heat kernel
for times below the distance and the bound one. -/
theorem latticeHeat_le_exp {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) (x y : Vertex 2) :
    latticeHeat t x y ≤
      3 * Real.exp (T / 18) * Real.exp (-‖latticeEuclideanEmbedding (y - x)‖ / 18) := by
  have hn : ‖latticeEuclideanEmbedding (y - x)‖ = ‖Rigidity.Green.edz x y‖ := by
    rw [latticeEuclideanEmbedding_sub, ← norm_neg, neg_sub]
  rw [hn]
  by_cases h : t ≤ ‖Rigidity.Green.edz x y‖
  · calc latticeHeat t x y ≤ 3 * Real.exp (-(‖Rigidity.Green.edz x y‖ / 18)) :=
          Rigidity.Green.openHeat_le_exp_of_le_norm _ ht h
      _ ≤ 3 * Real.exp (T / 18) * Real.exp (-‖Rigidity.Green.edz x y‖ / 18) := by
          rw [mul_assoc, neg_div]
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp (by linarith))
  · have h' := not_le.mp h
    have h1 : 1 ≤ Real.exp (T / 18 + -‖Rigidity.Green.edz x y‖ / 18) :=
      Real.one_le_exp (by linarith)
    calc latticeHeat t x y ≤ 1 := Rigidity.Green.openHeat_le_one _ ht.le x y
      _ ≤ 3 * Real.exp (T / 18) * Real.exp (-‖Rigidity.Green.edz x y‖ / 18) := by
          rw [mul_assoc, ← Real.exp_add]
          linarith

/-- `|Φ_{r²} * ∇u(x)|`, with the `ℓ¹` norm of the two components of the gradient. -/
noncomputable def heatGradient (u : Vertex 2 → ℝ) (r : ℝ) (x : Vertex 2) : ℝ :=
  ∑ j : Fin 2, |∑' y, latticeHeat (r ^ 2) x y * (u (y + LatticeProb.unit j) - u y)|

theorem heatGradient_nonneg (u : Vertex 2 → ℝ) (r : ℝ) (x : Vertex 2) : 0 ≤ heatGradient u r x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem measurable_heatGradient {F : Vertex 2 → Configuration 2 → ℝ} (hF : ∀ z, Measurable (F z))
    (x : Vertex 2) :
    Measurable fun rω : ℝ × Configuration 2 => heatGradient (fun z => F z rω.2) rω.1 x := by
  unfold heatGradient
  refine Finset.measurable_sum _ fun j _ => (Measurable.tsum fun y => ?_).abs
  exact (((continuous_latticeHeat x y).measurable.comp (measurable_fst.pow_const 2))).mul
    (((hF _).sub (hF y)).comp measurable_snd)

theorem measurable_heatGradient_const {F : Vertex 2 → Configuration 2 → ℝ}
    (hF : ∀ z, Measurable (F z)) (r : ℝ) (x : Vertex 2) :
    Measurable fun ω => heatGradient (fun z => F z ω) r x :=
  (measurable_heatGradient hF x).comp (f := fun ω => (r, ω)) (measurable_const.prodMk measurable_id)

theorem two_rpow_sub_one_mul_two {q : ℝ} (hq : 1 ≤ q) :
    (2 : ℝ≥0∞) ^ (q - 1) * 2 = 2 ^ q := by
  have h : ∀ t : ℝ, 0 ≤ t → (2 : ℝ≥0∞) ^ t = ENNReal.ofReal (2 ^ t) := fun t ht => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) ht, ENNReal.ofReal_ofNat]
  rw [h _ (by linarith), h _ (by linarith), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by positivity), Real.rpow_sub_one (by norm_num),
    div_mul_cancel₀ _ (by norm_num)]

/-- The moments of the heat-kernel averages of the sums of two neighbouring nonnegative variables
with uniform moments, for probability weights `w`. -/
theorem lintegral_heatSum_rpow_le {p : unitInterval} {w : Vertex 2 → ℝ≥0∞} (hw1 : ∑' y, w y = 1)
    {σ : Vertex 2 → Configuration 2 → ℝ≥0∞} (hσm : ∀ y, Measurable (σ y)) {A k q : ℝ} (hq : 1 ≤ q)
    (hA : 0 ≤ A) (hmom : ∀ y, ∫⁻ ω, σ y ω ^ q ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) :
    ∫⁻ ω, (∑ j : Fin 2, ∑' y, w y * (σ (y + LatticeProb.unit j) ω + σ y ω)) ^ q
        ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((4 * A * q ^ k) ^ q) := by
  have hq0 : 0 < q := by linarith
  set g : Fin 2 → Vertex 2 → Configuration 2 → ℝ≥0∞ := fun j y ω =>
    σ (y + LatticeProb.unit j) ω + σ y ω with hg
  have hgm : ∀ j y, Measurable (g j y) := fun j y => (hσm _).add (hσm _)
  have hgmom : ∀ j y, ∫⁻ ω, g j y ω ^ q ∂latticeBondLaw 2 p ≤
      2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) := by
    intro j y
    calc ∫⁻ ω, g j y ω ^ q ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, 2 ^ (q - 1) * (σ (y + LatticeProb.unit j) ω ^ q + σ y ω ^ q) ∂latticeBondLaw 2 p :=
          lintegral_mono fun ω => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
      _ = 2 ^ (q - 1) * (∫⁻ ω, σ (y + LatticeProb.unit j) ω ^ q ∂latticeBondLaw 2 p +
            ∫⁻ ω, σ y ω ^ q ∂latticeBondLaw 2 p) := by
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
  have hTj : ∀ j, ∫⁻ ω, (∑' y, w y * g j y ω) ^ q ∂latticeBondLaw 2 p ≤
      2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) := by
    intro j
    calc ∫⁻ ω, (∑' y, w y * g j y ω) ^ q ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, ∑' y, w y * g j y ω ^ q ∂latticeBondLaw 2 p := lintegral_mono (hJ j)
      _ = ∑' y, w y * ∫⁻ ω, g j y ω ^ q ∂latticeBondLaw 2 p := by
          rw [lintegral_tsum fun y => (((hgm j y).pow_const q).const_mul _).aemeasurable]
          exact tsum_congr fun y => lintegral_const_mul' _ _
            (ne_top_of_le_ne_top ENNReal.one_ne_top (hw1 ▸ ENNReal.le_tsum y))
      _ ≤ ∑' y, w y * (2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q)) :=
          ENNReal.tsum_le_tsum fun y => mul_le_mul_right (hgmom j y) _
      _ = 2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) := by rw [ENNReal.tsum_mul_right, hw1, one_mul]
  have hsplit : ∀ ω, (∑ j : Fin 2, ∑' y, w y * g j y ω) ^ q ≤
      2 ^ (q - 1) * ((∑' y, w y * g 0 y ω) ^ q + (∑' y, w y * g 1 y ω) ^ q) := by
    intro ω
    rw [Fin.sum_univ_two]
    exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
  have h2 : (2 : ℝ≥0∞) ^ q = ENNReal.ofReal (2 ^ q) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq0.le, ENNReal.ofReal_ofNat]
  have e4 : (4 * A * q ^ k) ^ q = 2 ^ q * 2 ^ q * (A * q ^ k) ^ q := by
    rw [show 4 * A * q ^ k = 2 * 2 * (A * q ^ k) by ring,
      Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by norm_num) (by norm_num)]
  calc ∫⁻ ω, (∑ j : Fin 2, ∑' y, w y * g j y ω) ^ q ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, 2 ^ (q - 1) * ((∑' y, w y * g 0 y ω) ^ q + (∑' y, w y * g 1 y ω) ^ q)
          ∂latticeBondLaw 2 p := lintegral_mono hsplit
    _ = 2 ^ (q - 1) * (∫⁻ ω, (∑' y, w y * g 0 y ω) ^ q ∂latticeBondLaw 2 p +
          ∫⁻ ω, (∑' y, w y * g 1 y ω) ^ q ∂latticeBondLaw 2 p) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          ENNReal.ofNat_ne_top), lintegral_add_left
          ((Measurable.tsum fun y => (hgm 0 y).const_mul _).pow_const q)]
    _ ≤ 2 ^ (q - 1) * (2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) +
          2 ^ q * ENNReal.ofReal ((A * q ^ k) ^ q)) :=
        mul_le_mul_right (add_le_add (hTj 0) (hTj 1)) _
    _ = ENNReal.ofReal ((4 * A * q ^ k) ^ q) := by
        rw [← two_mul, ← mul_assoc, ← mul_assoc, two_rpow_sub_one_mul_two hq, h2,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), e4]

/-- A nonnegative variable dominated almost surely by a variable with moments `(A q^k)^q` satisfies
the moment hypothesis of `isOsBond_of_moment_le`, hence is `O_s(C)`. -/
theorem isOsBond_of_ae_ofReal_le {p : unitInterval} {A k s C : ℝ} (hA : 0 ≤ A)
    (hmom : ∀ X : Configuration 2 → ℝ, Measurable X → (∀ ω, 0 ≤ X ω) →
      (∀ q : ℝ, 1 ≤ q → Integrable (fun ω => X ω ^ q) (latticeBondLaw 2 p) ∧
        ∫ ω, X ω ^ q ∂latticeBondLaw 2 p ≤ (A * q ^ k) ^ q) → IsOsBond 2 p X s C)
    {E : Configuration 2 → ℝ} (hEm : Measurable E) (hE0 : ∀ ω, 0 ≤ E ω)
    {T : Configuration 2 → ℝ≥0∞} (hpt : ∀ᵐ ω ∂latticeBondLaw 2 p, ENNReal.ofReal (E ω) ≤ T ω)
    (hT : ∀ q : ℝ, 1 ≤ q → ∫⁻ ω, T ω ^ q ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) :
    IsOsBond 2 p E s C := by
  refine hmom E hEm hE0 fun q hq => ?_
  have hq0 : 0 < q := by linarith
  have hmq : Measurable fun ω => E ω ^ q := hEm.pow_const q
  have hnn : 0 ≤ᵐ[latticeBondLaw 2 p] fun ω => E ω ^ q :=
    Eventually.of_forall fun ω => Real.rpow_nonneg (hE0 ω) q
  have hlin : ∫⁻ ω, ENNReal.ofReal (E ω ^ q) ∂latticeBondLaw 2 p ≤
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

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The gradient of the coarsened corrector along a lattice edge is at most the sums of (5.10) at
its endpoints. -/
theorem ofReal_abs_coarseField_step_le {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) {i : Fin 2} {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) (y : Vertex 2) (j : Fin 2) :
    ENNReal.ofReal |coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω| ≤
      stepSixSum Λ (y + LatticeProb.unit j) ω + stepSixSum Λ y ω := by
  set q : Fin 2 → ℝ := Pi.single i 1
  set b := shiftedAnchor 0 ω 0
  have hb : ω ∈ infiniteComponentEvent b := infinite_shiftedAnchor_zero hP 0
  have e : ∀ u, shiftedAnchor 0 ω u = planarCoarseAnchor ω u := fun u => by
    rw [shiftedAnchor_zero, guardAnchor_of_event hP]
  set w : Vertex 2 → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv q ω x b else 0 with hw
  have hW : ∀ u, coarseField hG hGv i 0 u ω = w (planarCoarseAnchor ω u) := by
    intro u
    simp only [hw, coarseField]
    rw [if_pos (infinite_planarCoarseAnchor hP u), e u]
  rw [hW, hW]
  have hnear : ∀ k, |(y + LatticeProb.unit j) k - y k| ≤ 1 := by
    intro k
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply, add_sub_cancel_left]
    split_ifs <;> simp
  have h := abs_coarse_step_le hP w hnear
  calc ENNReal.ofReal |w (planarCoarseAnchor ω (y + LatticeProb.unit j)) -
        w (planarCoarseAnchor ω y)|
      ≤ ENNReal.ofReal (edgeVariationIn ω (planarPartCube ω (y + LatticeProb.unit j)).ninefold.vertices w +
          edgeVariationIn ω (planarPartCube ω y).ninefold.vertices w) := ENNReal.ofReal_le_ofReal h
    _ ≤ ENNReal.ofReal (edgeVariationIn ω
            (planarPartCube ω (y + LatticeProb.unit j)).ninefold.vertices w) +
          ENNReal.ofReal (edgeVariationIn ω (planarPartCube ω y).ninefold.vertices w) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add
        (ofReal_edgeVariationIn_le_stepSixSum hG hGv hω hP hb hΛ0 hΛ _)
        (ofReal_edgeVariationIn_le_stepSixSum hG hGv hω hP hb hΛ0 hΛ _)

/-- The heat-kernel average of the gradient of the coarsened corrector is at most the heat-kernel
average of the sums of (5.10) at the endpoints of the edges. -/
theorem ofReal_heatGradient_le {ω : Configuration 2} (hω : ω ∈ G) (hP : PlanarPartitionEvent ω)
    {i : Fin 2} {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) (r : ℝ) (x : Vertex 2) :
    ENNReal.ofReal (heatGradient (fun z => coarseField hG hGv i 0 z ω) r x) ≤
      ∑ j : Fin 2, ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y) *
        (stepSixSum Λ (y + LatticeProb.unit j) ω + stepSixSum Λ y ω) := by
  unfold heatGradient
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
  refine Finset.sum_le_sum fun j _ => (ofReal_abs_tsum_le _).trans
    (ENNReal.tsum_le_tsum fun y => ?_)
  rw [abs_mul, abs_of_nonneg (latticeHeat_nonneg (sq_nonneg r) x y),
    ENNReal.ofReal_mul (latticeHeat_nonneg (sq_nonneg r) x y)]
  exact mul_le_mul_right (ofReal_abs_coarseField_step_le hG hGv hω hP hΛ0 hΛ y j) _

/-- **The heat-kernel averages of the gradient of the coarsened corrector are `O_s(C)`**,
uniformly in the radius and the point (the bound used by Dario for `r ≤ 1`). -/
theorem heatGradient_coarseField_isOsBond (hR3 : ArmstrongDarioOrderZeroTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ (i : Fin 2) (r : ℝ) (x : Vertex 2),
      IsOsBond 2 p (fun ω => heatGradient (fun z => coarseField hG hGv i 0 z ω) r x) s C := by
  obtain ⟨Λ, A, k, hA0, hk0, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hR3 hpc hp1 hGae
  have hs0 : 0 < 1 / (2 * k) := by positivity
  have hsk : 1 / (2 * k) * k < 1 := by field_simp; linarith
  obtain ⟨C, hC, hmom⟩ := isOsBond_of_moment_le (d := 2) (p := p) (by positivity : 0 < 4 * A)
    hs0 hsk
  refine ⟨1 / (2 * k), C, hs0, hC, fun i r x => ?_⟩
  have hEm := measurable_heatGradient_const (fun z => measurable_coarseField hG hGv i 0 z) r x
  have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  have hpt : ∀ᵐ ω ∂latticeBondLaw 2 p,
      ENNReal.ofReal (heatGradient (fun z => coarseField hG hGv i 0 z ω) r x) ≤
        ∑ j : Fin 2, ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y) *
          (stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω) := by
    filter_upwards [hGae, ae_planarPartitionEvent hpc, hall] with ω hω hP hl
    exact ofReal_heatGradient_le hG hGv hω hP (fun x => hΛ0 i x ω) hl r x
  exact isOsBond_of_ae_ofReal_le (by positivity) hmom hEm (fun ω => heatGradient_nonneg _ _ _) hpt
    fun q hq => lintegral_heatSum_rpow_le (tsum_ofReal_latticeHeat (sq_nonneg r) x)
      (fun y => measurable_stepSixSum (hΛm i) y) hq hA0.le (fun y => hmom6 i y q hq)

/-- **The heat-kernel averages of the gradient of the coarsened corrector converge**: almost
surely, for every point, direction and radius, `Σ_y Φ(r², x, y) ∇_j[χ]_𝒫(y)` converges
absolutely, since `Φ(r², x, ·)` decays exponentially and the sums of (5.10) have bounded means. -/
theorem ae_summable_heat_coarseField (hR3 : ArmstrongDarioOrderZeroTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (i : Fin 2) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (x : Vertex 2) (j : Fin 2) (r : ℝ), 0 < r →
      Summable fun y => latticeHeat (r ^ 2) x y *
        (coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω) := by
  obtain ⟨Λ, A, k, -, -, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hR3 hpc hp1 hGae
  have hgm : ∀ (j : Fin 2) (y : Vertex 2), Measurable fun ω =>
      stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω := fun j y =>
    (measurable_stepSixSum (hΛm i) _).add (measurable_stepSixSum (hΛm i) _)
  have h1 : ∀ v, ∫⁻ ω, stepSixSum (Λ i) v ω ∂latticeBondLaw 2 p ≤ ENNReal.ofReal A := by
    intro v
    have := hmom6 i v 1 le_rfl
    simpa only [ENNReal.rpow_one, Real.one_rpow, mul_one, Real.rpow_one] using this
  have hfin : ∀ (x : Vertex 2) (j : Fin 2), ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∑' y, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (y - x)‖ / 18)) *
        (stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω) < ∞ := by
    intro x j
    refine ae_lt_top (Measurable.tsum fun y => (hgm j y).const_mul _) ?_
    rw [lintegral_tsum fun y => ((hgm j y).const_mul _).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' y : Vertex 2,
      ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (y - x)‖ / 18)) *
        (2 * ENNReal.ofReal A)) ?_ ?_
    · rw [ENNReal.tsum_mul_right]
      exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (tsum_exp_neg_norm_sub_le x (by norm_num : (0 : ℝ) < 18)))
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
    · refine ENNReal.tsum_le_tsum fun y => ?_
      rw [lintegral_const_mul _ (hgm j y),
        lintegral_add_left (measurable_stepSixSum (hΛm i) _)]
      exact mul_le_mul_right (by rw [two_mul]; exact add_le_add (h1 _) (h1 _)) _
  have hfin' : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (x : Vertex 2) (j : Fin 2),
      ∑' y, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (y - x)‖ / 18)) *
        (stepSixSum (Λ i) (y + LatticeProb.unit j) ω + stepSixSum (Λ i) y ω) < ∞ :=
    ae_all_iff.2 fun x => ae_all_iff.2 fun j => hfin x j
  have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  filter_upwards [hGae, ae_planarPartitionEvent hpc, hall, hfin'] with ω hω hP hl hf x j r hr
  have hs : Summable fun y => Real.exp (-‖latticeEuclideanEmbedding (y - x)‖ / 18) *
      |coarseField hG hGv i 0 (y + LatticeProb.unit j) ω - coarseField hG hGv i 0 y ω| := by
    refine (ENNReal.summable_toReal (ne_top_of_le_ne_top (hf x j).ne
      (ENNReal.tsum_le_tsum fun y => ?_))).congr fun y => ENNReal.toReal_ofReal (by positivity)
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul_right
      (ofReal_abs_coarseField_step_le hG hGv hω hP (fun x => hΛ0 i x ω) hl y j) _
  refine summable_abs_iff.mp (Summable.of_nonneg_of_le (fun y => abs_nonneg _) (fun y => ?_)
    (hs.mul_left (3 * Real.exp (r ^ 2 / 18))))
  rw [abs_mul, abs_of_nonneg (latticeHeat_nonneg (sq_nonneg r) x y), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (latticeHeat_le_exp (pow_pos hr 2) le_rfl x y)
    (abs_nonneg _)

end Carrier

/-- The normalized oscillation `3^{-2m} Σ_{z ∈ □_m} |u(z) - (u)_{□_m}|^q` of a function. -/
noncomputable def boxOscFun (u : Vertex 2 → ℝ) (m : ℕ) (q : ℝ) : ℝ :=
  (∑ z ∈ boxAt 0 m, |u z - (∑ w ∈ boxAt 0 m, u w) / 9 ^ m| ^ q) / 9 ^ m

/-- **The multiscale Poincaré inequality of Dario, Proposition 2.19 (2.26), in cube form at
`R = 3^m`** (hypothesis: Dario proves the continuum version in Appendix A from Armstrong, Kuusi
and Mourrat, Proposition D.1 and Remark D.6, and Gilbarg and Trudinger, Lemma 7.12 and
Proposition 9.9, and states that the lattice version follows by standard arguments), with the
bound `C(d, q) ≤ A₀ q^{3/2}` for `q ≥ 2`. The convolutions `Φ_{r²} * ∇u` of (2.26) are required
to converge absolutely. -/
def MultiscalePoincareTwo (A₀ : ℝ) : Prop :=
  ∀ u : Vertex 2 → ℝ, (∀ (x : Vertex 2) (j : Fin 2) (r : ℝ), 0 < r →
      Summable fun y => latticeHeat (r ^ 2) x y * (u (y + LatticeProb.unit j) - u y)) →
    ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ, 2 ≤ q →
    ENNReal.ofReal (boxOscFun u m q) ≤
      ENNReal.ofReal ((A₀ * q ^ (3 / 2 : ℝ)) ^ q) *
        ∑' x : Vertex 2, ENNReal.ofReal
          (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / 9 ^ m) *
          (∫⁻ r in Ioc 0 (2 * 3 ^ m), ENNReal.ofReal (r * heatGradient u r x ^ 2)) ^ (q / 2)

/-- **Dario's Proposition 3.1 in dimension two** for the coarsened correctors (hypothesis):
`|Φ_{r²} * ∇[χ_{e_i}]_𝒫(x)| ≤ O_s(C/r)` for `r ≥ 1`, on every measurable conull carrier of the
qualitative corrector input. -/
def DarioPropThreeOneTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
      (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
        ∀ (i : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
          IsOsBond 2 p (fun ω => heatGradient (fun z => coarseField hG hGv i 0 z ω) r x) s (C / r)

/-- **Dario's Theorem 1 in dimension two** from the qualitative corrector input (R2), the
order-zero regularity input (R3), the multiscale Poincaré inequality and Proposition 3.1. -/
theorem darioOptimalCorrectorTwo_of_prop31 (hR2 : SupercriticalBondCorrectorInputTwo)
    (hR3 : ArmstrongDarioOrderZeroTwo) {A₀ : ℝ} (hA₀ : 0 < A₀) (hMSP : MultiscalePoincareTwo A₀)
    (h31 : DarioPropThreeOneTwo) : DarioOptimalCorrectorTwo := by
  refine darioOptimalCorrectorTwo_of_poincareInputs hR2 hR3 fun p hpc hp1 G hG hGv hGae => ?_
  obtain ⟨s₁, C₁, hs₁, hC₁, h1⟩ := h31 p hpc hp1 G hG hGv hGae
  obtain ⟨s₂, C₂, hs₂, hC₂, h2⟩ := heatGradient_coarseField_isOsBond hG hGv hR3 hpc hp1 hGae
  set s := min s₁ s₂
  have hs : 0 < s := lt_min hs₁ hs₂
  set C := max C₁ C₂ * 6 ^ (1 / s)
  have hC : 0 < C := mul_pos (lt_max_of_lt_left hC₁) (by positivity)
  refine ⟨fun i r x ω => heatGradient (fun z => coarseField hG hGv i 0 z ω) r x, A₀, C, s, hA₀, hC,
    hs, fun i x => measurable_heatGradient (fun z => measurable_coarseField hG hGv i 0 z) x,
    fun i r x ω => heatGradient_nonneg _ _ _,
    fun i m hm q hq => (ae_summable_heat_coarseField hG hGv hR3 hpc hp1 hGae i).mono fun ω hω =>
      hMSP (fun z => coarseField hG hGv i 0 z ω) hω m hm q hq,
    fun i r hr x => ?_, fun i r _ _ x => ?_⟩
  · have hm := measurable_heatGradient_const (fun z => measurable_coarseField hG hGv i 0 z) r x
    have := IsOsBond.mono_exponent hs (min_le_left _ _) hm (h1 i r hr x)
    refine IsOsBond.mono_scale hs (by have := div_pos hC₁ (by linarith : (0 : ℝ) < r); positivity)
      ?_ hm this
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) (by linarith)
  · have hm := measurable_heatGradient_const (fun z => measurable_coarseField hG hGv i 0 z) r x
    have := IsOsBond.mono_exponent hs (min_le_right _ _) hm (h2 i r x)
    exact IsOsBond.mono_scale hs (by positivity) (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity)) hm this

end Rigidity.Corrector
