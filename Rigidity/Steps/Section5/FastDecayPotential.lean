import Rigidity.Steps.Section5.FastDecayDichotomy
import Rigidity.Proofs.S2.ContinuumGreen
import LatticeProb.Prob.Percolation.LatticeBondErgodicity
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Percolation.OpenGraphTranslation
import LatticeProb.Prob.Percolation.LatticeUniqueClusterEvent
import LatticeProb.External.SupercriticalBondCorrectorInput
import Rigidity.Steps.Section5.FastDecay
import Rigidity.Steps.Section5.GradientTrichotomy
import Rigidity.Proofs.Section5.LogGrowth
import Rigidity.Proofs.Section5.GreenFamily
import Rigidity.Proofs.Section5.SublinearLiouville
import Rigidity.Proofs.Section5.PotentialLaplacian
import Rigidity.Proofs.Section5.Annulus

/-!
# Proposition 5.3: the steps of the fast-decay dichotomy for the potential

Proposition 5.3 (`FastDecayPotentialStmt`, corrected draft L1508-1515, proof L1656-1672) is proved
(`fastDecayPotential_of_steps`) from Proposition 5.7 (`GradientTrichotomyStmt`), Proposition 5.8
(`TwoScaleExpansionStmt`) and the existence of corrected planes (`CorrectedPlanesExist`, from
`SupercriticalBondCorrectorInput` for `p_c < p < 1` by `correctedPlanesExist_of_input`).

* The slope. Proposition 5.7 holds for every fixed slope `p ≠ 0`; we take `p = e₁`. The ray
  `ℛ_p` is then the `e₁`-axis and `Σ_y f(y) ℓ_p(y)` is the coefficient
  `M₁ = Σ_y f(y) ℓ_{e₁}(y)` of Proposition 5.8 itself, so the uniqueness of corrected planes
  modulo constants (needed for `Σ f ℓ_p = Σᵢ pᵢ Mᵢ` when `Σ f = 0`) is not used.
* `step:5.3-ray` (proved). In `d = 2`, `Ḡ(v) = -log |v| / (2πκ)`, so
  `∇Ḡ(v) · w = -v · w / (2πκ |v|²)` (`fderiv_greenBar_two`). Along `ℛ_p`,
  `Σᵢ Mᵢ ∂ᵢḠ(R p) = -(2πκ)⁻¹ |R p|⁻¹ Σᵢ (pᵢ / |p|) Mᵢ` exactly (`sum_mul_fderiv_greenBar_ray`),
  and at `n e₁`, `Σᵢ Mᵢ ∂ᵢḠ(n e₁) = -(2πκ)⁻¹ |n e₁|⁻¹ M₁` (`sum_mul_fderiv_greenBar_axisPoint`):
  `c = -(2πκ)⁻¹ ≠ 0` and no `o(|x|⁻¹)` term.
* `ClusterMeetsAxis` (not in the paper; proved by `clusterMeetsAxis_of_uniqueClusterAe`). The
  printed proof evaluates `u_f` at the points of `ℤ²` on the ray, which have to lie in `𝒞_∞`.
  Almost surely `n e₁ ∈ 𝒞_∞` for infinitely many `n ∈ ℕ`: this event is invariant under the
  translation by `e₁`, so it has probability `0` or `1` (ergodicity,
  `latticeBondLaw_zero_or_one_of_translationInvariant`); its probability is at least
  `θ = P[0 ∈ 𝒞_∞]` (translation invariance), and `θ > 0` since almost surely some vertex lies in
  an infinite cluster.
* Proposition 5.5 is not used: the first alternative of Proposition 5.3 is `Σ f ≠ 0`
  (Proposition 5.5 is used for Theorem 5.1, `fastDecayDichotomy_of_steps`). The almost-sure
  uniqueness of the infinite cluster is part of the statement of Proposition 5.7.

Assembly. On `Σ f = 0`, Proposition 5.7 for `ℓ_{e₁}` gives either a limit `L` with `u_f - L` of
finite support (eq. `compactly-supported`, `eventuallyZero_of_support_finite`), or `M₁ ≠ 0`.
In the second case Proposition 5.8 gives `L` with `|u_f(x) - L + Σᵢ Mᵢ ∂ᵢḠ(x)| ≤ C |x|^{-5/4}`
for `|x| ≥ 𝓜_f`; since `|∂ᵢḠ(x)| ≤ (2πκ |x|₂)⁻¹`, `u_f → L` (`tendsto_of_twoScaleExpansion`), and
at `x = n e₁ ∈ 𝒞_∞`, `n |u_f(x) - L| ≥ |M₁| / (2πκ) - C n^{-1/4}`, which is eq. `linear-decay`
with `c = |M₁| / (4πκ)` (`linearDecay_of_twoScaleExpansion`).

Consequences (`fastDecayDichotomy_of_props`, `fastDecay_of_props`): for `p_c < p < 1`,
Theorem 5.1 and Theorem 1.3 follow from Propositions 5.7 and 5.8 and the literature inputs of the
proved steps (Proposition 5.5, the Green family, sublinear Liouville).

The slope `e₁`. The proof uses Proposition 5.7 at `q = e₁` only, so each reduction has a form
whose hypothesis is that conclusion, `GradientTrichotomyAt p f e₁` for finitely supported `f`
(`fastDecayPotential_of_steps_e1`, `fastDecayDichotomy_of_props_e1`, `fastDecay_of_props_e1`);
the forms with `GradientTrichotomyStmt` are derived from them.
-/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology
open scoped RealInnerProductSpace

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.Section2

variable {ω : Configuration 2}

/-! ### step:5.3-ray: the gradient of the homogenized Green function in the plane -/

/-- `∇Ḡ(v) · w = -v · w / (2πκ |v|²)` off the pole (`d = 2`). -/
theorem fderiv_greenBar_two (κ : {a : ℝ // 0 < a}) {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (greenBar 2 le_rfl κ) v w = -⟪v, w⟫ / (2 * Real.pi * κ.val * ‖v‖ ^ 2) := by
  have hκ := κ.2
  have hF : ∀ u : EuclideanSpace ℝ (Fin 2), u ≠ 0 →
      greenBar 2 le_rfl κ u = (fun t => -Real.log t / (4 * Real.pi * κ.val)) (‖u‖ ^ 2) := by
    intro u hu
    simp only [greenBar, continuumGreen, dif_pos hu, if_true, Real.log_pow]
    field_simp
    ring
  have hΦ : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => -Real.log t / (4 * Real.pi * κ.val))
      (-(1 / (4 * Real.pi * κ.val)) * t ^ (-(1 : ℝ))) t := by
    intro t ht
    rw [Real.rpow_neg_one]
    refine (((Real.hasDerivAt_log ht.ne').neg).div_const (4 * Real.pi * κ.val)).congr_deriv ?_
    ring
  have hn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  rw [(Rigidity.Proofs.S2.hasFDerivAt_of_radial hF hΦ hv).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Real.rpow_neg_one]
  field_simp
  ring

/-- `|∂ᵢḠ(x)| ≤ (2πκ |x|₂)⁻¹` at a lattice point `x ≠ 0`. -/
theorem abs_fderiv_greenBar_le (κ : {a : ℝ // 0 < a}) {x : Vertex 2} (hx : 0 < eucl x)
    (i : Fin 2) :
    |fderiv ℝ (greenBar 2 le_rfl κ) (toReal x) (EuclideanSpace.single i 1)| ≤
      (2 * Real.pi * κ.val)⁻¹ * (eucl x)⁻¹ := by
  have hκ := κ.2
  have hnorm : ‖toReal x‖ = eucl x := rfl
  have hv : toReal x ≠ 0 := norm_pos_iff.mp (hnorm ▸ hx)
  rw [fderiv_greenBar_two κ hv, hnorm, EuclideanSpace.inner_single_right]
  have hi : |(toReal x) i| ≤ eucl x := abs_coord_le_eucl x i
  rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi * κ.val * eucl x ^ 2)]
  simp only [one_mul, RCLike.conj_to_real]
  rw [div_le_iff₀ (by positivity)]
  calc |(toReal x) i| ≤ eucl x := hi
    _ = (2 * Real.pi * κ.val)⁻¹ * (eucl x)⁻¹ * (2 * Real.pi * κ.val * eucl x ^ 2) := by
      field_simp

/-- Step `step:5.3-ray`: along the ray `ℛ_p` (`p ≠ 0`, `R > 0`),
`Σᵢ Mᵢ ∂ᵢḠ(R p) = -(2πκ)⁻¹ |R p|⁻¹ Σᵢ (pᵢ / |p|) Mᵢ`. -/
theorem sum_mul_fderiv_greenBar_ray (κ : {a : ℝ // 0 < a}) (M : Fin 2 → ℝ)
    {q : EuclideanSpace ℝ (Fin 2)} (hq : q ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∑ i, M i * fderiv ℝ (greenBar 2 le_rfl κ) (R • q) (EuclideanSpace.single i 1) =
      -(2 * Real.pi * κ.val)⁻¹ * ‖R • q‖⁻¹ * ∑ i, (q i / ‖q‖) * M i := by
  have hκ := κ.2
  have hq0 : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hv : R • q ≠ 0 := smul_ne_zero hR.ne' hq
  simp only [fderiv_greenBar_two κ hv, EuclideanSpace.inner_single_right, one_mul,
    RCLike.conj_to_real, norm_smul, Real.norm_eq_abs, abs_of_pos hR, PiLp.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- The lattice point `n e₁`. -/
def axisPoint (n : ℕ) : Vertex 2 := Pi.single 0 (n : ℤ)

theorem axisPoint_apply_zero (n : ℕ) : axisPoint n 0 = n := by simp [axisPoint]

theorem axisPoint_apply_one (n : ℕ) : axisPoint n 1 = 0 := by simp [axisPoint]

theorem l1_axisPoint (n : ℕ) : l1 (axisPoint n) = n := by
  simp [l1, Fin.sum_univ_two, axisPoint_apply_zero, axisPoint_apply_one]

theorem eucl_axisPoint (n : ℕ) : eucl (axisPoint n) = n := by
  rw [eucl, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [latticeEuclideanEmbedding, axisPoint_apply_zero, axisPoint_apply_one]

/-- Step `step:5.3-ray` on the `e₁`-axis: `Σᵢ Mᵢ ∂ᵢḠ(n e₁) = -(2πκ)⁻¹ |n e₁|⁻¹ M₁`. -/
theorem sum_mul_fderiv_greenBar_axisPoint (κ : {a : ℝ // 0 < a}) (M : Fin 2 → ℝ) {n : ℕ}
    (hn : 0 < n) :
    ∑ i, M i * fderiv ℝ (greenBar 2 le_rfl κ) (toReal (axisPoint n))
        (EuclideanSpace.single i 1) =
      -(2 * Real.pi * κ.val)⁻¹ * (l1 (axisPoint n))⁻¹ * M 0 := by
  have hκ := κ.2
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnorm : ‖toReal (axisPoint n)‖ = n := eucl_axisPoint n
  have hv : toReal (axisPoint n) ≠ 0 := norm_pos_iff.mp (hnorm ▸ hn')
  have h0 : (toReal (axisPoint n)) 0 = n := by
    change ((axisPoint n 0 : ℤ) : ℝ) = n
    rw [axisPoint_apply_zero, Int.cast_natCast]
  have h1 : (toReal (axisPoint n)) 1 = 0 := by
    change ((axisPoint n 1 : ℤ) : ℝ) = 0
    rw [axisPoint_apply_one, Int.cast_zero]
  simp only [fderiv_greenBar_two κ hv, EuclideanSpace.inner_single_right, one_mul,
    RCLike.conj_to_real, Fin.sum_univ_two, hnorm, h0, h1, l1_axisPoint]
  field_simp
  ring

/-! ### The infinite cluster meets the `e₁`-axis (not in the paper) -/

/-- Almost surely the infinite cluster contains `n e₁` for arbitrarily large `n`. -/
def ClusterMeetsAxis (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ axisPoint n ∈ (uniqueInfiniteComponent h).supp

theorem infiniteComponentEvent_configurationTranslation_iff (z : Vertex 2) (ω : Configuration 2)
    (x : Vertex 2) :
    configurationTranslation z ω ∈ infiniteComponentEvent x ↔
      ω ∈ infiniteComponentEvent (x - z) := by
  simp only [mem_infiniteComponentEvent_iff, openGraph_reachable_sub_translation_iff]
  constructor
  · intro h s
    obtain ⟨y, hy, hr⟩ := h (s.image (· + z))
    exact ⟨y - z, fun hs => hy (Finset.mem_image.mpr ⟨y - z, hs, sub_add_cancel y z⟩), hr⟩
  · intro h s
    obtain ⟨y, hy, hr⟩ := h (s.image (· - z))
    refine ⟨y + z, fun hs => hy (Finset.mem_image.mpr ⟨y + z, hs, add_sub_cancel_right y z⟩), ?_⟩
    rwa [add_sub_cancel_right]

/-- `P[x lies in an infinite cluster]` does not depend on `x`. -/
theorem measure_infiniteComponentEvent_eq (p : unitInterval) (x : Vertex 2) :
    latticeBondLaw 2 p (infiniteComponentEvent x) =
      latticeBondLaw 2 p (infiniteComponentEvent 0) := by
  have h := (measurePreserving_configurationTranslation p (-x)).measure_preimage
    (measurableSet_infiniteComponentEvent (0 : Vertex 2)).nullMeasurableSet
  have hpre : configurationTranslation (-x) ⁻¹' infiniteComponentEvent (0 : Vertex 2) =
      infiniteComponentEvent x := by
    ext ω
    rw [Set.mem_preimage, infiniteComponentEvent_configurationTranslation_iff, zero_sub, neg_neg]
  rw [← h, hpre]

theorem axisPoint_succ_sub (n : ℕ) : axisPoint (n + 1) - axisPoint 1 = axisPoint n := by
  ext i
  fin_cases i <;> simp [axisPoint]

/-- The vertices `N e₁, (N + 1) e₁, …` of which one lies in an infinite cluster. -/
def axisTail (N : ℕ) : Set (Configuration 2) :=
  ⋃ n, ⋃ (_ : N ≤ n), infiniteComponentEvent (axisPoint n)

/-- The event that `n e₁` lies in an infinite cluster for infinitely many `n`. -/
def axisEvent : Set (Configuration 2) := ⋂ N, axisTail N

theorem measurableSet_axisTail (N : ℕ) : MeasurableSet (axisTail N) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
    measurableSet_infiniteComponentEvent _

theorem mem_axisEvent_iff (ω : Configuration 2) :
    ω ∈ axisEvent ↔ ∀ N : ℕ, ∃ n, N ≤ n ∧ ω ∈ infiniteComponentEvent (axisPoint n) := by
  simp [axisEvent, axisTail]

theorem preimage_axisEvent :
    configurationTranslation (axisPoint 1) ⁻¹' axisEvent = axisEvent := by
  ext ω
  simp only [Set.mem_preimage, mem_axisEvent_iff,
    infiniteComponentEvent_configurationTranslation_iff]
  constructor
  · intro h N
    obtain ⟨n, hn, hω⟩ := h (N + 1)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨m, by omega, by rwa [axisPoint_succ_sub] at hω⟩
  · intro h N
    obtain ⟨n, hn, hω⟩ := h N
    exact ⟨n + 1, by omega, by rwa [axisPoint_succ_sub]⟩

/-- `ClusterMeetsAxis` from the almost-sure uniqueness of the infinite cluster, by ergodicity of
the translation by `e₁`. -/
theorem clusterMeetsAxis_of_uniqueClusterAe {p : unitInterval} (hU : UniqueClusterAe p) :
    ClusterMeetsAxis p := by
  set μ := latticeBondLaw 2 p
  have hmeas : MeasurableSet axisEvent := MeasurableSet.iInter measurableSet_axisTail
  -- `θ = P[0 ∈ 𝒞_∞] > 0`
  have hθ : μ (infiniteComponentEvent 0) ≠ 0 := by
    intro h0
    have hU0 : μ (⋃ x : Vertex 2, infiniteComponentEvent x) = 0 :=
      measure_iUnion_null fun x => (measure_infiniteComponentEvent_eq p x).trans h0
    have hae : ∀ᵐ ω ∂μ, ω ∈ ⋃ x : Vertex 2, infiniteComponentEvent x :=
      hU.mono fun ω h => Set.mem_iUnion.2 ((mem_uniqueInfiniteComponentEvent_iff ω).1 h).1
    have hc := measure_union_null hU0 (ae_iff.1 hae)
    rw [show (⋃ x : Vertex 2, infiniteComponentEvent x) ∪
        {ω | ω ∉ ⋃ x : Vertex 2, infiniteComponentEvent x} = Set.univ from
      Set.union_compl_self _, measure_univ] at hc
    exact one_ne_zero hc
  -- `P[axisEvent] ≥ θ`
  have hpos : μ axisEvent ≠ 0 := by
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (fun N => (measurableSet_axisTail N).nullMeasurableSet)
      (fun N N' hNN' => Set.iUnion_mono fun n => Set.iUnion_mono' fun hn => ⟨hNN'.trans hn, le_rfl⟩)
      ⟨0, measure_ne_top _ _⟩
    have hge : μ (infiniteComponentEvent 0) ≤ μ axisEvent :=
      ge_of_tendsto' hlim fun N => by
        rw [← measure_infiniteComponentEvent_eq p (axisPoint N)]
        exact measure_mono (Set.subset_iUnion₂_of_subset N le_rfl le_rfl)
    exact fun h => hθ (le_antisymm (h ▸ hge) bot_le)
  have hone : μ axisEvent = 1 :=
    ((latticeBondLaw_zero_or_one_of_translationInvariant p
      (z := axisPoint 1) (fun h => by simpa [axisPoint] using congr_fun h 0) hmeas
      preimage_axisEvent).resolve_left hpos)
  have hae : ∀ᵐ ω ∂μ, ω ∈ axisEvent := ae_iff.2 ((prob_compl_eq_zero_iff hmeas).2 hone)
  filter_upwards [hae] with ω hω h N
  obtain ⟨n, hn, hE⟩ := (mem_axisEvent_iff ω).1 hω N
  exact ⟨n, hn, (mem_uniqueInfiniteComponent_iff h _).2 hE⟩

/-! ### Corrected planes -/

/-- Almost surely the infinite cluster carries a corrected plane of each slope `eᵢ`. -/
def CorrectedPlanesExist (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ i : Fin 2,
    ∃ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ

/-- `CorrectedPlanesExist` in the supercritical regime, from the classification of `𝒜₁`. -/
theorem correctedPlanesExist_of_input (hC : LatticeProb.External.SupercriticalBondCorrectorInput)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    CorrectedPlanesExist p := by
  filter_upwards [hC 2 le_rfl p hp hp1] with ω hω h i
  have : Infinite (uniqueInfiniteComponent h) :=
    Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)
  obtain ⟨o⟩ := (inferInstance : Nonempty (uniqueInfiniteComponent h))
  obtain ⟨ℓ, hℓ, -⟩ := (hω h).1 (Pi.single i 1) o
  exact ⟨ℓ, hℓ.1⟩

/-! ### The deterministic assembly -/

/-- Eq. `compactly-supported` for a function of finite support. -/
theorem eventuallyZero_of_support_finite {C : OpenComponent ω} {v : C → ℝ}
    (hv : (Function.support v).Finite) : EventuallyZero C v :=
  exists_forall_eucl_ge_of_eventually
    (hv.eventually_cofinite_notMem.mono fun _ hx => Function.notMem_support.1 hx)

/-- A function with the two-scale expansion of Proposition 5.8 beyond some scale converges at
infinity. -/
theorem tendsto_of_twoScaleExpansion {C : OpenComponent ω} {u : C → ℝ} {L R₀ K : ℝ}
    (κ : {a : ℝ // 0 < a}) (M : Fin 2 → ℝ)
    (hexp : ∀ x : C, R₀ ≤ l1 x.val →
      |u x - L + ∑ i, M i * fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val)
          (EuclideanSpace.single i 1)| ≤ K * Real.rpow (l1 x.val) (-5 / 4)) :
    Tendsto u cofinite (𝓝 L) := by
  have hκ := κ.2
  set A := (2 * Real.pi * κ.val)⁻¹ * ∑ i, |M i| + |K| with hA
  have hA0 : 0 ≤ A := by positivity
  refine Metric.tendsto_nhds.2 fun ε hε => eventually_cofinite_of_forall_eucl_ge
    (R := max (max R₀ 1) (2 * A / ε + 1)) fun x hx => ?_
  have hR₀ : R₀ ≤ eucl x.val := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have h1 : 1 ≤ eucl x.val := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hAε : 2 * A / ε + 1 ≤ eucl x.val := (le_max_right _ _).trans hx
  have he0 : 0 < eucl x.val := one_pos.trans_le h1
  have hl1 : eucl x.val ≤ l1 x.val := eucl_le_l1 x.val
  have hgrad : |∑ i, M i * fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val)
      (EuclideanSpace.single i 1)| ≤
        (2 * Real.pi * κ.val)⁻¹ * (∑ i, |M i|) * (eucl x.val)⁻¹ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    calc |M i| * |fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val) (EuclideanSpace.single i 1)|
        ≤ |M i| * ((2 * Real.pi * κ.val)⁻¹ * (eucl x.val)⁻¹) :=
          mul_le_mul_of_nonneg_left (abs_fderiv_greenBar_le κ he0 i) (abs_nonneg _)
      _ = (2 * Real.pi * κ.val)⁻¹ * (|M i| * (eucl x.val)⁻¹) := by ring
  have hrpow : K * Real.rpow (l1 x.val) (-5 / 4) ≤ |K| * (eucl x.val)⁻¹ := by
    have h1' : 1 ≤ l1 x.val := h1.trans hl1
    have hr : Real.rpow (l1 x.val) (-5 / 4) ≤ (l1 x.val)⁻¹ := by
      rw [Real.rpow_eq_pow, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le h1' (by norm_num)
    have hr0 : 0 ≤ Real.rpow (l1 x.val) (-5 / 4) := Real.rpow_nonneg (l1_nonneg _) _
    calc K * Real.rpow (l1 x.val) (-5 / 4) ≤ |K| * Real.rpow (l1 x.val) (-5 / 4) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) hr0
      _ ≤ |K| * (l1 x.val)⁻¹ := mul_le_mul_of_nonneg_left hr (abs_nonneg K)
      _ ≤ |K| * (eucl x.val)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ he0 hl1) (abs_nonneg K)
  have hbound : |u x - L| ≤ A * (eucl x.val)⁻¹ := by
    have := hexp x (hR₀.trans hl1)
    have htri := abs_sub (u x - L + ∑ i, M i * fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val)
      (EuclideanSpace.single i 1)) (∑ i, M i * fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val)
      (EuclideanSpace.single i 1))
    rw [add_sub_cancel_right] at htri
    rw [hA]
    linarith
  rw [Real.dist_eq]
  calc |u x - L| ≤ A * (eucl x.val)⁻¹ := hbound
    _ < ε := by
      rw [← div_eq_mul_inv, div_lt_iff₀ he0]
      have : 2 * A / ε * ε = 2 * A := div_mul_cancel₀ _ hε.ne'
      nlinarith

/-- Eq. `linear-decay` from the two-scale expansion of Proposition 5.8 with `M₁ ≠ 0`, at the
points `n e₁` of the cluster (step `step:5.3-ray`). -/
theorem linearDecay_of_twoScaleExpansion {C : OpenComponent ω} {u : C → ℝ} {L R₀ K : ℝ}
    (κ : {a : ℝ // 0 < a}) (M : Fin 2 → ℝ) (hM : M 0 ≠ 0)
    (hexp : ∀ x : C, R₀ ≤ l1 x.val →
      |u x - L + ∑ i, M i * fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val)
          (EuclideanSpace.single i 1)| ≤ K * Real.rpow (l1 x.val) (-5 / 4))
    (haxis : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ axisPoint n ∈ C.supp) :
    LinearDecay C (fun x => u x - L) := by
  have hκ := κ.2
  set c := (2 * Real.pi * κ.val)⁻¹ * |M 0| / 2 with hc
  have hc0 : 0 < c := by have := abs_pos.mpr hM; positivity
  -- `|K| n^{-1/4} ≤ c` for large `n`
  have hlim : Tendsto (fun n : ℕ => |K| * (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).const_mul |K|
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hc0))
  refine ⟨c, hc0, fun R => ?_⟩
  obtain ⟨n, hn, hmem⟩ := haxis (max (max N₀ 1) (max ⌈R⌉₊ ⌈R₀⌉₊))
  have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hnR : R ≤ n := (Nat.le_ceil R).trans
    (Nat.cast_le.mpr ((le_max_left _ _).trans ((le_max_right _ _).trans hn)))
  have hnR₀ : R₀ ≤ n := (Nat.le_ceil R₀).trans
    (Nat.cast_le.mpr ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hN : |K| * (n : ℝ) ^ (-(1 / 4 : ℝ)) < c :=
    hN₀ n ((le_max_left _ _).trans ((le_max_left _ _).trans hn))
  set x : C := ⟨axisPoint n, hmem⟩
  have hl1 : l1 x.val = n := l1_axisPoint n
  refine ⟨x, hl1 ▸ hnR, ?_⟩
  have hexp' := hexp x (hl1 ▸ hnR₀)
  rw [sum_mul_fderiv_greenBar_axisPoint κ M hn1, hl1] at hexp'
  rw [hl1]
  -- `n · n^{-5/4} = n^{-1/4}`
  have hpow : (n : ℝ) * Real.rpow (n : ℝ) (-5 / 4) = (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_eq_pow, show (-(1 / 4 : ℝ)) = 1 + (-5 / 4) by norm_num,
      Real.rpow_add hnpos, Real.rpow_one]
  have hr0 : 0 ≤ Real.rpow (n : ℝ) (-5 / 4) := Real.rpow_nonneg hnpos.le _
  have hK : K * Real.rpow (n : ℝ) (-5 / 4) ≤ |K| * Real.rpow (n : ℝ) (-5 / 4) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hr0
  -- `(2πκ)⁻¹ |M₁| ≤ n |u(x) - L| + |K| n^{-1/4}`
  have htri : |(2 * Real.pi * κ.val)⁻¹ * (n : ℝ)⁻¹ * M 0| ≤
      |u x - L| + |u x - L + -(2 * Real.pi * κ.val)⁻¹ * (n : ℝ)⁻¹ * M 0| := by
    have := abs_sub (u x - L) (u x - L + -(2 * Real.pi * κ.val)⁻¹ * (n : ℝ)⁻¹ * M 0)
    rw [show u x - L - (u x - L + -(2 * Real.pi * κ.val)⁻¹ * (n : ℝ)⁻¹ * M 0) =
      (2 * Real.pi * κ.val)⁻¹ * (n : ℝ)⁻¹ * M 0 by ring] at this
    linarith [abs_nonneg (u x - L)]
  have habs : |(2 * Real.pi * κ.val)⁻¹ * (n : ℝ)⁻¹ * M 0| =
      (2 * Real.pi * κ.val)⁻¹ * |M 0| * (n : ℝ)⁻¹ := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi * κ.val)⁻¹),
      abs_of_pos (inv_pos.mpr hnpos)]
    ring
  rw [habs] at htri
  have hmul := mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl (hexp'.trans hK)))
    hnpos.le
  have hpow' : (n : ℝ) * (|K| * Real.rpow (n : ℝ) (-5 / 4)) = |K| * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [← hpow]; ring
  have hcancel : (n : ℝ) * ((2 * Real.pi * κ.val)⁻¹ * |M 0| * (n : ℝ)⁻¹) =
      (2 * Real.pi * κ.val)⁻¹ * |M 0| := by
    field_simp
  rw [mul_add, hcancel, hpow'] at hmul
  change c ≤ (n : ℝ) * |u x - L|
  rw [hc]
  linarith

/-- Proposition 5.3 from Proposition 5.7 at the slope `e₁` only (`GradientTrichotomyAt p f e₁`),
Proposition 5.8 and the existence of corrected planes. -/
theorem fastDecayPotential_of_steps_e1 {p : unitInterval} {f : Vertex 2 → ℤ}
    (h57 : (Function.support f).Finite → GradientTrichotomyAt p f (Pi.single 0 1))
    (h58 : TwoScaleExpansionStmt p f) (hplanes : CorrectedPlanesExist p) :
    FastDecayPotentialStmt p f := by
  intro hf
  have hU : UniqueClusterAe p := (h57 hf).mono fun _ h => h.1
  obtain ⟨K, s, -, -, κ, M, -, -, h58ae⟩ := h58 hf
  filter_upwards [h57 hf, h58ae, hplanes, clusterMeetsAxis_of_uniqueClusterAe hU] with
    ω H57 H58 HP HA
  obtain ⟨h, H57⟩ := H57
  obtain ⟨h', H58⟩ := H58
  refine ⟨h, fun G hG => ?_⟩
  by_cases hm : mass (uniqueInfiniteComponent h) f = 0
  swap
  · exact Or.inl hm
  right
  choose ℓ hℓ using HP h
  rcases H57 hm G hG (ℓ 0) (hℓ 0) with hpair | ⟨L, hL, hsupp⟩
  · obtain ⟨L, hL⟩ := H58 hm G hG ℓ hℓ
    exact ⟨L, tendsto_of_twoScaleExpansion κ _ hL,
      Or.inl (linearDecay_of_twoScaleExpansion κ _ hpair hL (HA h))⟩
  · exact ⟨L, hL, Or.inr (eventuallyZero_of_support_finite hsupp)⟩

/-- Proposition 5.3 from Propositions 5.7 and 5.8 and the existence of corrected planes
(through `fastDecayPotential_of_steps_e1`: Proposition 5.7 is used at `q = e₁` only). -/
theorem fastDecayPotential_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (h57 : GradientTrichotomyStmt p f) (h58 : TwoScaleExpansionStmt p f)
    (hplanes : CorrectedPlanesExist p) : FastDecayPotentialStmt p f :=
  fastDecayPotential_of_steps_e1
    (fun hf => h57 hf _ fun h => by simpa using congr_fun h 0) h58 hplanes

/-- Theorem 5.1 from Proposition 5.7 at the slope `e₁` only and Proposition 5.8 for
`p_c < p < 1`: Proposition 5.3 by `fastDecayPotential_of_steps_e1`, Proposition 5.5 by
`logGrowth`. -/
theorem fastDecayDichotomy_of_props_e1
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h57 : ∀ f, (Function.support f).Finite → GradientTrichotomyAt p f (Pi.single 0 1))
    (h58 : ∀ f, TwoScaleExpansionStmt p f) :
    FastDecayDichotomyStmt p :=
  fastDecayDichotomy_of_steps
    (fun f => fastDecayPotential_of_steps_e1 (h57 f) (h58 f)
      (correctedPlanesExist_of_input hCorr hp hp1))
    (Rigidity.Proofs.Section5.logGrowth hUq hGQ hp hp1)
    (Rigidity.Proofs.Section5.greenFamilyExists hE hp hp1)
    (Rigidity.Proofs.Section5.sublinearLiouville p hp hp1 hAD)
    Rigidity.Proofs.Section5.potentialLaplacian

/-- Theorem 5.1 from Propositions 5.7 and 5.8 for `p_c < p < 1`: Proposition 5.3 by
`fastDecayPotential_of_steps`, Proposition 5.5 by `logGrowth`. -/
theorem fastDecayDichotomy_of_props
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h57 : ∀ f, GradientTrichotomyStmt p f) (h58 : ∀ f, TwoScaleExpansionStmt p f) :
    FastDecayDichotomyStmt p :=
  fastDecayDichotomy_of_props_e1 hCorr hUq hGQ hE hAD hp hp1
    (fun f hf => h57 f hf _ fun h => by simpa using congr_fun h 0) h58

/-- Theorem 1.3 from Proposition 5.7 at the slope `e₁` only and Proposition 5.8 for
`p_c < p < 1`. -/
theorem fastDecay_of_props_e1
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h57 : ∀ f, (Function.support f).Finite → GradientTrichotomyAt p f (Pi.single 0 1))
    (h58 : ∀ f, TwoScaleExpansionStmt p f) :
    FastDecayStmt p :=
  fastDecay_of_steps (fastDecayDichotomy_of_props_e1 hCorr hUq hGQ hE hAD hp hp1 h57 h58)
    Rigidity.Proofs.Section5.annulusStep

/-- Theorem 1.3 from Propositions 5.7 and 5.8 for `p_c < p < 1`. -/
theorem fastDecay_of_props
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h57 : ∀ f, GradientTrichotomyStmt p f) (h58 : ∀ f, TwoScaleExpansionStmt p f) :
    FastDecayStmt p :=
  fastDecay_of_steps (fastDecayDichotomy_of_props hCorr hUq hGQ hE hAD hp hp1 h57 h58)
    Rigidity.Proofs.Section5.annulusStep

end Rigidity.Steps.Section5
