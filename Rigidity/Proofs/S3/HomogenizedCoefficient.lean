import Rigidity.Proofs.S3.FluxEvent
import Rigidity.Proofs.S3.EnergyIdentity
import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent
import LatticeProb.Prob.Percolation.OpenGraphTranslation

/-!
# The homogenized coefficient is positive

Proof of `HomogenizedCoefficientProposed` (`FluxEvent.lean`): the gradient
`X = (ℓ_{e₁}(e₁) - ℓ_{e₁}(0)) 1{(e₁, 0) ∈ E(C_∞)}` of the corrected plane of slope `e₁` is
integrable with positive mean `ā`. Notation: `X_k` is the gradient along `(e_k, 0)`, and
`n_N = 2N (2N + 1)^{d-1}` is the number of edges `(x, x + e_k)` of `Q_N`, for every `k`.

* **The box energy inequality** (`BoxEnergyInequality`, deterministic). Summation by parts on
  `Q_N` against `ℓ - x₁ - c` for the harmonic `ℓ` bounds the energy of `ℓ` in `Q_N` by the drift
  `∑ (ℓ(x + e₁) - ℓ(x))` plus `sup_{C ∩ Q_N} |ℓ - x₁ - c|` times the boundary flux `∑ |∇ℓ|`.
* **Stationarity.** All terms are sums of `X_k ∘ τ_{-x}` (`edgeDifference_add_eq`), so their
  means are `n_N E[X]`, `n_N ∑_k E[min(X_k², M)]` and `2 (2N + 1)^{d-1} ∑_k E|X_k|`.
* **The good event.** By the sublinearity of `ℓ - x₁` (`IsCorrectedPlane`), almost every
  configuration eventually lies in the event where the inequality holds with `η = ε (dN + 1)`;
  off this event, `X` is controlled by `E[(|X| - K)⁺] + K P(bad)`. Hence
  `E[X] ≥ ∑_k E[min(X_k², M)] - ε (d + 1) ∑_k E|X_k| - E[(|X| - K)⁺]`, and letting `ε → 0`,
  `K → ∞`, `E[X] ≥ ∑_k E[min(X_k², 1)]`.
* **Positivity.** If all `X_k` vanish almost surely, then `ℓ` is constant on the cluster;
  with positive probability `n e₁ ∈ C_∞` for infinitely many `n`, contradicting the slope `e₁`.

Integrability of `X_k` is Theorem 2.5 at the origin (`CorrectorQuantitativeInput`).

So `HomogenizedCoefficientProposed` is a theorem of the project, from literature inputs only
(`homogenizedCoefficientProposed hU hCorr hQ`); it is not an input of Proposition 3.2: it
discharges the hypothesis `hHom` of `fluxEventStep` (`FluxEvent.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation LatticeProb.External
  Rigidity.Section3 Rigidity.Steps.S3

namespace Rigidity.Proofs.S3

/-- **The box energy inequality** (deterministic; summation by parts on `Q_N` against
`ℓ - x₁ - c`). For a harmonic function `ℓ` on a cluster `C` with `|ℓ - x₁ - c| ≤ η` on
`C ∩ Q_N`, the energy of `ℓ` on the edges of `Q_N` is at most the drift
`∑_{x, x + e₁ ∈ Q_N} ∇ℓ(x + e₁, x)` plus `η` times the flux through the boundary edges. -/
def BoxEnergyInequality (d : ℕ) [NeZero d] : Prop :=
  ∀ (ω : Configuration d) (C : OpenComponent ω) (u : C → ℝ),
    (∀ x, componentLaplacian C u x = 0) → ∀ (N : ℕ) (c η : ℝ),
    (∀ a : C, a.val ∈ latticeCube d N → |u a - (a.val 0 : ℝ) - c| ≤ η) →
    ∑ k : Fin d, ∑ x ∈ (latticeCube d N).filter (fun x => x + unit k ∈ latticeCube d N),
        edgeDifference C u (x + unit k) x ^ 2 ≤
      ∑ x ∈ (latticeCube d N).filter (fun x => x + unit 0 ∈ latticeCube d N),
          edgeDifference C u (x + unit 0) x +
        η * ∑ k : Fin d,
          (∑ x ∈ (latticeCube d N).filter (fun x => x + unit k ∉ latticeCube d N),
              |edgeDifference C u x (x + unit k)| +
            ∑ x ∈ (latticeCube d N).filter (fun x => x - unit k ∉ latticeCube d N),
              |edgeDifference C u x (x - unit k)|)

namespace HomogenizedCoefficient

open FluxEvent

variable {d : ℕ}

section Boxes

/-- The sites `x ∈ Q_N` with `x + e_k ∈ Q_N`. -/
noncomputable def innerSites (N : ℕ) (k : Fin d) : Finset (Vertex d) :=
  (latticeCube d N).filter fun x => x + unit k ∈ latticeCube d N

/-- The sites `x ∈ Q_N` with `x + e_k ∉ Q_N`. -/
noncomputable def exitPlus (N : ℕ) (k : Fin d) : Finset (Vertex d) :=
  (latticeCube d N).filter fun x => x + unit k ∉ latticeCube d N

/-- The sites `x ∈ Q_N` with `x - e_k ∉ Q_N`. -/
noncomputable def exitMinus (N : ℕ) (k : Fin d) : Finset (Vertex d) :=
  (latticeCube d N).filter fun x => x - unit k ∉ latticeCube d N

theorem card_latticeCube (N : ℕ) : (latticeCube d N).card = (2 * N + 1) ^ d := by
  rw [latticeCube, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  congr 1
  omega

theorem card_exitPlus (N : ℕ) (k : Fin d) : (exitPlus N k).card = (2 * N + 1) ^ (d - 1) := by
  rw [← card_latticeCube_filter_eq N k (N : ℤ) (by omega) le_rfl]
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  rw [add_unit_mem_latticeCube_iff hx, not_not]

theorem card_exitMinus (N : ℕ) (k : Fin d) : (exitMinus N k).card = (2 * N + 1) ^ (d - 1) := by
  rw [← card_latticeCube_filter_eq N k (-(N : ℤ)) le_rfl (by omega)]
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  rw [sub_unit_mem_latticeCube_iff hx, not_not]

theorem card_innerSites [NeZero d] (N : ℕ) (k : Fin d) :
    (innerSites N k).card = 2 * N * (2 * N + 1) ^ (d - 1) := by
  have h := Finset.card_filter_add_card_filter_not (s := latticeCube d N)
    (fun x => x + unit k ∈ latticeCube d N)
  have hd1 : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne d))
  have h2 : (latticeCube d N).card = 2 * N * (2 * N + 1) ^ (d - 1) + (2 * N + 1) ^ (d - 1) := by
    rw [card_latticeCube, ← hd1, pow_succ', hd1]
    ring
  change (innerSites N k).card + (exitPlus N k).card = _ at h
  rw [card_exitPlus, h2] at h
  exact Nat.add_right_cancel h

theorem card_innerSites_real [NeZero d] (N : ℕ) (k : Fin d) :
    ((innerSites N k).card : ℝ) = 2 * N * (2 * N + 1) ^ (d - 1) := by
  rw [card_innerSites]
  push_cast
  ring

end Boxes

section Integrals

variable (p : unitInterval)

theorem integrable_sum_comp (s : Finset (Vertex d)) (z : Vertex d → Vertex d)
    {g : Configuration d → ℝ} (hg : Integrable g (latticeBondLaw d p)) :
    Integrable (fun ω => ∑ x ∈ s, g (configurationTranslation (z x) ω)) (latticeBondLaw d p) :=
  integrable_finsetSum s fun x _ =>
    (measurePreserving_configurationTranslation p (z x)).integrable_comp_of_integrable hg

theorem integral_sum_comp (s : Finset (Vertex d)) (z : Vertex d → Vertex d)
    {g : Configuration d → ℝ} (hg : Integrable g (latticeBondLaw d p)) :
    ∫ ω, ∑ x ∈ s, g (configurationTranslation (z x) ω) ∂latticeBondLaw d p =
      s.card * ∫ ω, g ω ∂latticeBondLaw d p := by
  rw [integral_finsetSum s (f := fun x ω => g (configurationTranslation (z x) ω)) fun x _ =>
    (measurePreserving_configurationTranslation p (z x)).integrable_comp_of_integrable hg]
  rw [Finset.sum_congr rfl fun x _ => integral_comp_mp
    (measurePreserving_configurationTranslation p (z x)) hg.aestronglyMeasurable,
    Finset.sum_const, nsmul_eq_mul]

end Integrals

section Field

variable [NeZero d]

/-- **Integrability of the gradients** (Theorem 2.5 with `α = 1` at the origin): the gradient
`X_k = ℓ_{e₁}(e_k) - ℓ_{e₁}(0)` along `(e_k, 0)` is at most `C (M + 2) + 1` for a minimal scale
`M ≤ O_s(C)`. -/
theorem integrable_edgeField_unit (hQ : Rigidity.External.CorrectorQuantitativeInput)
    (hd : 2 ≤ d) (p : unitInterval) (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {G : Set (Configuration d)} (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G)
    {Φ : Vertex d → Vertex d → Configuration d → ℝ} (hΦm : ∀ x y, Measurable (Φ x y))
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 d) u)
    (hΦ : IsEdgeField G Φ) (k : Fin d) :
    Integrable (Φ (unit k) 0) (latticeBondLaw d p) := by
  obtain ⟨s, C, hs, hC, hM⟩ := hQ d hd p hpc hp1 1 one_pos
  obtain ⟨M, hMm, hM0, hMos, hbound⟩ := hM 0
  refine Integrable.mono' ((((integrable_of_isOsBond hs hC hMm hM0 hMos).add
    (integrable_const 2)).const_mul C).add (integrable_const 1))
    (hΦm (unit k) 0).aestronglyMeasurable ?_
  filter_upwards [hGae, hbound] with ω hω hb
  obtain ⟨h, hexu⟩ := hex ω hω
  obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
  rw [← hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu, Real.norm_eq_abs]
  have hr : 0 ≤ C * (M ω + 2) := mul_nonneg hC.le (by linarith [hM0 ω])
  unfold edgeDifference
  split_ifs with h0
  · have h0' : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp h0.1 h0.2
    let a : uniqueInfiniteComponent h := ⟨unit k, h0.1⟩
    let b : uniqueInfiniteComponent h := ⟨0, h0'⟩
    have hna : ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding 0‖ < M ω + 2 :=
      (norm_latticeEuclideanEmbedding_unit_sub_zero k).trans_lt (by linarith [hM0 ω])
    have hnb : ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding 0‖ < M ω + 2 := by
      simp only [b, sub_self, norm_zero]
      linarith [hM0 ω]
    have hab : (componentGraph (uniqueInfiniteComponent h)).Adj a b :=
      ((uniqueInfiniteComponent h).toSimpleGraph_adj a.2 b.2).2 h0.2
    have hbd := hb h (slopeE1 d) u hu (M ω + 2) (by linarith) a b a b hna hnb hna hnb hab
    have hqa : ∑ i, slopeE1 d i * ((a.val i : ℤ) : ℝ) = (((unit k : Vertex d) 0 : ℤ) : ℝ) := by
      rw [Finset.sum_eq_single (0 : Fin d) (fun i _ hi => by simp [slopeE1, hi]) (by simp)]
      simp [slopeE1, a]
    have hqa1 : |(((unit k : Vertex d) 0 : ℤ) : ℝ)| ≤ 1 := by
      by_cases hk : k = 0
      · subst hk
        simp [unit]
      · simp [unit, Ne.symm hk]
    have hqb : ∑ i, slopeE1 d i * ((b.val i : ℤ) : ℝ) = 0 := by simp [b]
    have hq : ∑ i, |slopeE1 d i| = 1 := by
      rw [Finset.sum_eq_single (0 : Fin d) (fun i _ hi => by simp [slopeE1, hi]) (by simp)]
      simp [slopeE1]
    rw [hqa, hqb, hq, Real.rpow_one, sub_zero, mul_one] at hbd
    have ea : Rigidity.Section3.extend (uniqueInfiniteComponent h) u (unit k) = u a := dif_pos h0.1
    have eb : Rigidity.Section3.extend (uniqueInfiniteComponent h) u 0 = u b := dif_pos h0'
    rw [ea, eb]
    have h1 : |u a - (((unit k : Vertex d) 0 : ℤ) : ℝ) - u b| ≤ C * (M ω + 2) := by
      linarith [abs_nonneg (u a - (((unit k : Vertex d) 0 : ℤ) : ℝ) - u b)]
    calc |u a - u b| = |(u a - (((unit k : Vertex d) 0 : ℤ) : ℝ) - u b) +
          (((unit k : Vertex d) 0 : ℤ) : ℝ)| := by ring_nf
      _ ≤ |u a - (((unit k : Vertex d) 0 : ℤ) : ℝ) - u b| + |(((unit k : Vertex d) 0 : ℤ) : ℝ)| :=
          abs_add_le _ _
      _ ≤ C * (M ω + 2) + 1 := add_le_add h1 hqa1
  · rw [abs_zero]
    show (0 : ℝ) ≤ C * (M ω + 2) + 1
    linarith [hr]

/-- The gradient along `(x + e_k, x)` is `X_k` at the configuration translated by `-x`. -/
theorem edgeDifference_add_unit {G : Set (Configuration d)}
    {Φ : Vertex d → Vertex d → Configuration d → ℝ} (hΦ : IsEdgeField G Φ)
    {ω : Configuration d} (hω : ∀ z, configurationTranslation z ω ∈ G) (C : OpenComponent ω)
    (hC : C.supp.Infinite) (u : C → ℝ) (hu : IsCorrectedPlane C (slopeE1 d) u) (x : Vertex d)
    (k : Fin d) :
    edgeDifference C u (x + unit k) x = Φ (unit k) 0 (configurationTranslation (-x) ω) := by
  have := edgeDifference_add_eq hΦ hω C hC u hu (unit k) 0 x
  rwa [add_comm (unit k) x, zero_add] at this

/-- The drift `∑_{x, x + e₁ ∈ Q_N} X ∘ τ_{-x}`. -/
noncomputable def driftSum (Φ : Vertex d → Vertex d → Configuration d → ℝ) (N : ℕ)
    (ω : Configuration d) : ℝ :=
  ∑ x ∈ innerSites N 0, Φ (unit 0) 0 (configurationTranslation (-x) ω)

/-- The truncated energy `∑_k ∑_{x, x + e_k ∈ Q_N} min(X_k², M) ∘ τ_{-x}`. -/
noncomputable def truncEnergy (Φ : Vertex d → Vertex d → Configuration d → ℝ) (N : ℕ) (M : ℝ)
    (ω : Configuration d) : ℝ :=
  ∑ k, ∑ x ∈ innerSites N k, min (Φ (unit k) 0 (configurationTranslation (-x) ω) ^ 2) M

/-- The boundary flux `∑ |∇ℓ|` over the edges leaving `Q_N`. -/
noncomputable def boundarySum (Φ : Vertex d → Vertex d → Configuration d → ℝ) (N : ℕ)
    (ω : Configuration d) : ℝ :=
  ∑ k, (∑ x ∈ exitPlus N k, |Φ (unit k) 0 (configurationTranslation (-x) ω)| +
    ∑ x ∈ exitMinus N k, |Φ (unit k) 0 (configurationTranslation (-(x - unit k)) ω)|)

/-- The event where the box energy inequality holds with constant `η`. -/
def goodSet (Φ : Vertex d → Vertex d → Configuration d → ℝ) (N : ℕ) (M η : ℝ) :
    Set (Configuration d) :=
  {ω | truncEnergy Φ N M ω - η * boundarySum Φ N ω ≤ driftSum Φ N ω}

theorem measurableSet_goodSet (p : unitInterval) {Φ : Vertex d → Vertex d → Configuration d → ℝ}
    (hΦm : ∀ x y, Measurable (Φ x y)) (N : ℕ) (M η : ℝ) : MeasurableSet (goodSet Φ N M η) := by
  have hτ : ∀ z : Vertex d, Measurable (configurationTranslation z) := fun z =>
    (measurePreserving_configurationTranslation p z).measurable
  refine measurableSet_le ?_ ?_
  · refine (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun x _ =>
      (((hΦm _ _).comp (hτ _)).pow_const 2).min measurable_const).sub
      (measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_))
    exact (Finset.measurable_sum _ fun x _ => ((hΦm _ _).comp (hτ _)).abs).add
      (Finset.measurable_sum _ fun x _ => ((hΦm _ _).comp (hτ _)).abs)
  · exact Finset.measurable_sum _ fun x _ => (hΦm _ _).comp (hτ _)

end Field

section Bound

variable [NeZero d]

/-- **Pointwise lower bound for the drift.** On the good event this is the box energy inequality;
off it, `X ≥ -(|X| - K)⁺ - K` and the truncated energy is at most `d n_N M`. -/
theorem driftSum_ge (Φ : Vertex d → Vertex d → Configuration d → ℝ) (N : ℕ) {M η K : ℝ}
    (hη : 0 ≤ η) (ω : Configuration d) :
    truncEnergy Φ N M ω - η * boundarySum Φ N ω -
      ∑ x ∈ innerSites N 0, max (|Φ (unit 0) 0 (configurationTranslation (-x) ω)| - K) 0 -
      (d * (2 * N * (2 * N + 1) ^ (d - 1)) * M + 2 * N * (2 * N + 1) ^ (d - 1) * K) *
        (goodSet Φ N M η)ᶜ.indicator 1 ω ≤ driftSum Φ N ω := by
  classical
  have hB : 0 ≤ boundarySum Φ N ω := Finset.sum_nonneg fun k _ =>
    add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hS : 0 ≤ ∑ x ∈ innerSites N 0,
      max (|Φ (unit 0) 0 (configurationTranslation (-x) ω)| - K) 0 :=
    Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hηB := mul_nonneg hη hB
  rw [Set.indicator_apply]
  by_cases hω : ω ∈ goodSet Φ N M η
  · rw [if_neg (show ω ∉ (goodSet Φ N M η)ᶜ from fun h => h hω), mul_zero, sub_zero]
    have h : truncEnergy Φ N M ω - η * boundarySum Φ N ω ≤ driftSum Φ N ω := hω
    linarith
  · rw [if_pos (show ω ∈ (goodSet Φ N M η)ᶜ from hω), Pi.one_apply, mul_one]
    have hT : truncEnergy Φ N M ω ≤ d * (2 * N * (2 * N + 1) ^ (d - 1)) * M := by
      calc truncEnergy Φ N M ω ≤ ∑ k : Fin d, ∑ x ∈ innerSites N k, M :=
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun x _ => min_le_right _ _
        _ = d * (2 * N * (2 * N + 1) ^ (d - 1)) * M := by
            simp only [Finset.sum_const, nsmul_eq_mul, card_innerSites_real, Finset.card_univ,
              Fintype.card_fin]
            ring
    have h1 : ∑ x ∈ innerSites N 0,
        (-(max (|Φ (unit 0) 0 (configurationTranslation (-x) ω)| - K) 0) - K) ≤
          driftSum Φ N ω := Finset.sum_le_sum fun x _ => by
      have := le_max_left (|Φ (unit 0) 0 (configurationTranslation (-x) ω)| - K) 0
      have := neg_abs_le (Φ (unit 0) 0 (configurationTranslation (-x) ω))
      linarith
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul,
      card_innerSites_real] at h1
    linarith

/-- **The fixed-`N` bound in mean** (stationarity): with `n_N = 2N (2N + 1)^{d-1}`,
`n_N E[X] ≥ n_N ∑_k E[min(X_k², M)] - 2η (2N + 1)^{d-1} ∑_k E|X_k| - n_N E[(|X| - K)⁺]
- (d n_N M + n_N K) P(bad)`. -/
theorem integral_bound (p : unitInterval) {Φ : Vertex d → Vertex d → Configuration d → ℝ}
    (hΦm : ∀ x y, Measurable (Φ x y))
    (hXi : ∀ k, Integrable (Φ (unit k) 0) (latticeBondLaw d p)) (N : ℕ) {M η K : ℝ}
    (hM : 0 ≤ M) (hη : 0 ≤ η) (hK : 0 ≤ K) :
    2 * N * (2 * N + 1) ^ (d - 1) *
        (∑ k, ∫ ω, min (Φ (unit k) 0 ω ^ 2) M ∂latticeBondLaw d p) -
      η * (2 * (2 * N + 1) ^ (d - 1) * ∑ k, ∫ ω, |Φ (unit k) 0 ω| ∂latticeBondLaw d p) -
      2 * N * (2 * N + 1) ^ (d - 1) * ∫ ω, max (|Φ (unit 0) 0 ω| - K) 0 ∂latticeBondLaw d p -
      (d * (2 * N * (2 * N + 1) ^ (d - 1)) * M + 2 * N * (2 * N + 1) ^ (d - 1) * K) *
        (latticeBondLaw d p).real (goodSet Φ N M η)ᶜ ≤
      2 * N * (2 * N + 1) ^ (d - 1) * ∫ ω, Φ (unit 0) 0 ω ∂latticeBondLaw d p := by
  set μ := latticeBondLaw d p
  have iMin : ∀ k, Integrable (fun ω => min (Φ (unit k) 0 ω ^ 2) M) μ := fun k =>
    (integrable_const M).mono'
      ((((hΦm _ _).pow_const 2).min measurable_const).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) hM)]
        exact min_le_right _ _)
  have iAbs : ∀ k, Integrable (fun ω => |Φ (unit k) 0 ω|) μ := fun k => (hXi k).abs
  have iMax : Integrable (fun ω => max (|Φ (unit 0) 0 ω| - K) 0) μ :=
    (hXi 0).abs.mono' (((hΦm _ _).abs.sub_const K).max measurable_const).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (abs_nonneg _))
  have hmeas := measurableSet_goodSet p hΦm N M η
  have iT : Integrable (fun ω => truncEnergy Φ N M ω) μ :=
    integrable_finsetSum Finset.univ fun k _ => (integrable_sum_comp p _ (fun x => -x) (iMin k) :)
  have iB : Integrable (fun ω => boundarySum Φ N ω) μ :=
    integrable_finsetSum Finset.univ fun k _ =>
      ((integrable_sum_comp p _ (fun x => -x) (iAbs k)).add
        (integrable_sum_comp p _ (fun x => -(x - unit k)) (iAbs k) :))
  have iS : Integrable (fun ω => ∑ x ∈ innerSites N 0,
      max (|Φ (unit 0) 0 (configurationTranslation (-x) ω)| - K) 0) μ :=
    (integrable_sum_comp p _ (fun x => -x) iMax :)
  have iI : Integrable (fun ω => (goodSet Φ N M η)ᶜ.indicator (1 : Configuration d → ℝ) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hmeas.compl
  have iD : Integrable (fun ω => driftSum Φ N ω) μ := (integrable_sum_comp p _ (fun x => -x) (hXi 0) :)
  have eT : ∫ ω, truncEnergy Φ N M ω ∂μ =
      2 * N * (2 * N + 1) ^ (d - 1) * ∑ k, ∫ ω, min (Φ (unit k) 0 ω ^ 2) M ∂μ := by
    unfold truncEnergy
    rw [integral_finsetSum _ fun k _ => integrable_sum_comp p _ (fun x => -x) (iMin k),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (integral_sum_comp p _ (fun x => -x) (iMin k)).trans (by rw [card_innerSites_real])
  have eB : ∫ ω, boundarySum Φ N ω ∂μ =
      2 * (2 * N + 1) ^ (d - 1) * ∑ k, ∫ ω, |Φ (unit k) 0 ω| ∂μ := by
    unfold boundarySum
    rw [integral_finsetSum _ (f := fun k ω =>
      ∑ x ∈ exitPlus N k, |Φ (unit k) 0 (configurationTranslation (-x) ω)| +
        ∑ x ∈ exitMinus N k, |Φ (unit k) 0 (configurationTranslation (-(x - unit k)) ω)|)
      fun k _ => ((integrable_sum_comp p _ (fun x => -x) (iAbs k)).add
        (integrable_sum_comp p _ (fun x => -(x - unit k)) (iAbs k) :)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add (integrable_sum_comp p _ (fun x => -x) (iAbs k))
      (integrable_sum_comp p _ (fun x => -(x - unit k)) (iAbs k))]
    rw [(integral_sum_comp p _ (fun x => -x) (iAbs k)).trans rfl,
      (integral_sum_comp p _ (fun x => -(x - unit k)) (iAbs k)).trans rfl,
      card_exitPlus, card_exitMinus]
    push_cast
    ring
  have eS : ∫ ω, (∑ x ∈ innerSites N 0,
      max (|Φ (unit 0) 0 (configurationTranslation (-x) ω)| - K) 0) ∂μ =
      2 * N * (2 * N + 1) ^ (d - 1) * ∫ ω, max (|Φ (unit 0) 0 ω| - K) 0 ∂μ :=
    (integral_sum_comp p _ (fun x => -x) iMax).trans (by rw [card_innerSites_real])
  have eD : ∫ ω, driftSum Φ N ω ∂μ = 2 * N * (2 * N + 1) ^ (d - 1) * ∫ ω, Φ (unit 0) 0 ω ∂μ :=
    (integral_sum_comp p _ (fun x => -x) (hXi 0)).trans (by rw [card_innerSites_real])
  have i1 : Integrable (fun ω => truncEnergy Φ N M ω - η * boundarySum Φ N ω) μ :=
    iT.sub (iB.const_mul η)
  have i2 : Integrable (fun ω => truncEnergy Φ N M ω - η * boundarySum Φ N ω -
      ∑ x ∈ innerSites N 0, max (|Φ (unit 0) 0 (configurationTranslation (-x) ω)| - K) 0) μ :=
    i1.sub iS
  have i3 : Integrable (fun ω =>
      (d * (2 * N * (2 * N + 1) ^ (d - 1)) * M + 2 * N * (2 * N + 1) ^ (d - 1) * K) *
        (goodSet Φ N M η)ᶜ.indicator (1 : Configuration d → ℝ) ω) μ := iI.const_mul _
  have i4 : Integrable (fun ω => truncEnergy Φ N M ω - η * boundarySum Φ N ω -
      ∑ x ∈ innerSites N 0, max (|Φ (unit 0) 0 (configurationTranslation (-x) ω)| - K) 0 -
      (d * (2 * N * (2 * N + 1) ^ (d - 1)) * M + 2 * N * (2 * N + 1) ^ (d - 1) * K) *
        (goodSet Φ N M η)ᶜ.indicator (1 : Configuration d → ℝ) ω) μ := i2.sub i3
  have hmono := integral_mono i4 iD (fun ω => driftSum_ge Φ N hη ω)
  rw [integral_sub i2 i3, integral_sub i1 iS, integral_sub iT (iB.const_mul η),
    integral_const_mul, integral_const_mul, integral_indicator_one hmeas.compl, eT, eB, eS,
    eD] at hmono
  exact hmono

end Bound

section Limit

theorem dist_latticeEuclideanEmbedding_zero_le (x : Vertex d) :
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding (0 : Vertex d)) ≤
      ∑ j, |((x j : ℤ) : ℝ)| := by
  rw [dist_eq_norm, ← latticeEuclideanEmbedding_sub, sub_zero, EuclideanSpace.norm_eq]
  have h : ∀ j, ‖latticeEuclideanEmbedding x j‖ = |((x j : ℤ) : ℝ)| := fun j => by
    rw [Real.norm_eq_abs]
    rfl
  simp only [h]
  calc √(∑ j, |((x j : ℤ) : ℝ)| ^ 2) ≤ √((∑ j, |((x j : ℤ) : ℝ)|) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _)
    _ = ∑ j, |((x j : ℤ) : ℝ)| := Real.sqrt_sq (Finset.sum_nonneg fun j _ => abs_nonneg _)

theorem dist_lt_of_mem_latticeCube {N : ℕ} {x : Vertex d} (hx : x ∈ latticeCube d N) :
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding (0 : Vertex d)) <
      d * N + 1 := by
  refine (dist_latticeEuclideanEmbedding_zero_le x).trans_lt ?_
  have h : ∀ j, |((x j : ℤ) : ℝ)| ≤ N := fun j => by
    have := (mem_latticeCube.1 hx) j
    exact abs_le.2 ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  calc ∑ j, |((x j : ℤ) : ℝ)| ≤ ∑ _j : Fin d, (N : ℝ) := Finset.sum_le_sum fun j _ => h j
    _ = d * N := by simp
    _ < d * N + 1 := lt_add_one _

variable [NeZero d]

theorem componentSlope_slopeE1 {ω : Configuration d} (C : OpenComponent ω) (a : C) :
    componentSlope C (slopeE1 d) a = ((a.val 0 : ℤ) : ℝ) := by
  unfold componentSlope
  rw [Finset.sum_eq_single (0 : Fin d) (fun i _ hi => by simp [slopeE1, hi]) (by simp)]
  simp [slopeE1]

/-- **The good event holds eventually.** By the sublinearity of `ℓ - x₁`, almost every
configuration lies in the good event with `η = ε (dN + 1)` for every large `N`. -/
theorem ae_eventually_mem_goodSet (hE : BoxEnergyInequality d) (p : unitInterval)
    {G : Set (Configuration d)} {Φ : Vertex d → Vertex d → Configuration d → ℝ}
    (hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ z, configurationTranslation z ω ∈ G)
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 d) u)
    (hΦ : IsEdgeField G Φ) (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ᶠ N : ℕ in atTop, ω ∈ goodSet Φ N M (ε * (d * N + 1)) := by
  filter_upwards [hall] with ω hω
  have hω0 : ω ∈ G := by simpa [configurationTranslation_zero] using hω 0
  obtain ⟨h, hexu⟩ := hex ω hω0
  have hC : (uniqueInfiniteComponent h).supp.Infinite := uniqueInfiniteComponent_infinite h
  obtain ⟨u, hu⟩ := hexu _ hC
  obtain ⟨R₀, -, hR⟩ := hu.2 ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge R₀
  refine eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hR' : R₀ ≤ d * N + 1 := by
    have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hosc : ∀ a : uniqueInfiniteComponent h, a.val ∈ latticeCube d N →
      |u a - ((a.val 0 : ℤ) : ℝ) - 0| ≤ ε * (d * N + 1) := by
    intro a ha
    have hball : a ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 (d * N + 1) :=
      (mem_componentEuclideanBall _ 0 _ a).2 (dist_lt_of_mem_latticeCube ha)
    have := hR _ hR' a hball
    rwa [componentSlope_slopeE1, ← sub_zero (u a - _)] at this
  have hineq := hE ω (uniqueInfiniteComponent h) u hu.1.1 N 0 (ε * (d * N + 1)) hosc
  have e1 : ∀ k x, edgeDifference (uniqueInfiniteComponent h) u (x + unit k) x =
      Φ (unit k) 0 (configurationTranslation (-x) ω) := fun k x =>
    edgeDifference_add_unit hΦ hω _ hC u hu x k
  have e2 : ∀ k x, |edgeDifference (uniqueInfiniteComponent h) u x (x + unit k)| =
      |Φ (unit k) 0 (configurationTranslation (-x) ω)| := by
    intro k x
    rw [edgeDifference_antisymm _ u (x + unit k) x, abs_neg, e1]
  have e3 : ∀ k x, |edgeDifference (uniqueInfiniteComponent h) u x (x - unit k)| =
      |Φ (unit k) 0 (configurationTranslation (-(x - unit k)) ω)| := by
    intro k x
    have := e1 k (x - unit k)
    rw [sub_add_cancel] at this
    rw [this]
  simp only [e1, e2, e3] at hineq
  have hT : truncEnergy Φ N M ω ≤ ∑ k, ∑ x ∈ innerSites N k,
      Φ (unit k) 0 (configurationTranslation (-x) ω) ^ 2 :=
    Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun x _ => min_le_left _ _
  show truncEnergy Φ N M ω - ε * (d * N + 1) * boundarySum Φ N ω ≤ driftSum Φ N ω
  unfold driftSum boundarySum
  unfold innerSites at hT
  unfold innerSites exitPlus exitMinus
  linarith

end Limit

section Energy

variable [NeZero d]

omit [NeZero d] in
/-- `E[(|X| - K)⁺] → 0` as `K → ∞` (dominated convergence). -/
theorem tendsto_integral_excess (p : unitInterval) {X : Configuration d → ℝ} (hXm : Measurable X)
    (hX : Integrable X (latticeBondLaw d p)) :
    Tendsto (fun K : ℕ => ∫ ω, max (|X ω| - K) 0 ∂latticeBondLaw d p) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun ω => |X ω|)
    (F := fun (K : ℕ) ω => max (|X ω| - K) 0) (f := fun _ => (0 : ℝ))
    (fun K => ((hXm.abs.sub_const _).max measurable_const).aestronglyMeasurable) hX.abs
    (fun K => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]) (abs_nonneg _))
    (ae_of_all _ fun ω => tendsto_const_nhds.congr' (eventually_atTop.2 ⟨⌈|X ω|⌉₊, fun K hK => by
      have : |X ω| ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK)
      exact (max_eq_right (by linarith)).symm⟩))
  simpa using h

/-- **The energy bound** `E[X] ≥ ∑_k E[min(X_k², M)]`: the fixed-`N` bound in mean, the good
event (whose complement has probability `→ 0`), then `ε → 0` and `K → ∞`. -/
theorem integral_ge_energy (hE : BoxEnergyInequality d) (p : unitInterval)
    {G : Set (Configuration d)} {Φ : Vertex d → Vertex d → Configuration d → ℝ}
    (hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ z, configurationTranslation z ω ∈ G)
    (hΦm : ∀ x y, Measurable (Φ x y))
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 d) u)
    (hΦ : IsEdgeField G Φ) (hXi : ∀ k, Integrable (Φ (unit k) 0) (latticeBondLaw d p))
    {M : ℝ} (hM : 0 ≤ M) :
    ∑ k, ∫ ω, min (Φ (unit k) 0 ω ^ 2) M ∂latticeBondLaw d p ≤
      ∫ ω, Φ (unit 0) 0 ω ∂latticeBondLaw d p := by
  set μ := latticeBondLaw d p
  set E := ∑ k, ∫ ω, min (Φ (unit k) 0 ω ^ 2) M ∂μ
  set B := ∑ k, ∫ ω, |Φ (unit k) 0 ω| ∂μ
  have hB : 0 ≤ B := Finset.sum_nonneg fun k _ => integral_nonneg fun ω => abs_nonneg _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have step1 : ∀ ε : ℝ, 0 < ε → ∀ K : ℕ,
      E - ε * (d + 1) * B - ∫ ω, max (|Φ (unit 0) 0 ω| - K) 0 ∂μ ≤ ∫ ω, Φ (unit 0) 0 ω ∂μ := by
    intro ε hε K
    set mK := ∫ ω, max (|Φ (unit 0) 0 ω| - K) 0 ∂μ
    have hP : Tendsto (fun N : ℕ => μ.real (goodSet Φ N M (ε * (d * N + 1)))ᶜ) atTop (𝓝 0) := by
      have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := μ)
        (A := ∅) (L := atTop) MeasurableSet.empty
        (fun N : ℕ => (measurableSet_goodSet p hΦm N M (ε * (d * N + 1))).compl)
        (by
          filter_upwards [ae_eventually_mem_goodSet hE p hall hex hΦ M hε] with ω hω
          filter_upwards [hω] with N hN
          simp [hN])
      rw [measure_empty] at h
      have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
      simpa [Function.comp_def, measureReal_def] using h'
    have hlim : Tendsto (fun N : ℕ => E - ε * (d + 1) * B - mK -
        (d * M + K) * μ.real (goodSet Φ N M (ε * (d * N + 1)))ᶜ) atTop
        (𝓝 (E - ε * (d + 1) * B - mK)) := by
      have := (tendsto_const_nhds (x := E - ε * (d + 1) * B - mK)).sub
        (hP.const_mul (d * M + K))
      simpa using this
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
    have hb := integral_bound p hΦm hXi N hM (η := ε * (d * N + 1)) (by positivity)
      (Nat.cast_nonneg K)
    set b : ℝ := (2 * N + 1) ^ (d - 1)
    set P := μ.real (goodSet Φ N M (ε * (d * N + 1)))ᶜ
    have hbpos : 0 < b := by positivity
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hn : 0 < 2 * N * b := by positivity
    have hk : ε * (d * N + 1) * (2 * b * B) ≤ 2 * N * b * (ε * (d + 1) * B) := by
      have h1 : (d * N + 1 : ℝ) ≤ (d + 1) * N := by nlinarith
      have h2 : 0 ≤ 2 * ε * b * B := by positivity
      nlinarith
    rw [← mul_le_mul_iff_of_pos_left hn]
    calc 2 * N * b * (E - ε * (d + 1) * B - mK - (d * M + K) * P)
        = 2 * N * b * E - 2 * N * b * (ε * (d + 1) * B) - 2 * N * b * mK -
          (d * (2 * N * b) * M + 2 * N * b * K) * P := by ring
      _ ≤ 2 * N * b * E - ε * (d * N + 1) * (2 * b * B) - 2 * N * b * mK -
          (d * (2 * N * b) * M + 2 * N * b * K) * P := by linarith
      _ ≤ 2 * N * b * ∫ ω, Φ (unit 0) 0 ω ∂μ := hb
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨K, hK⟩ := ((tendsto_integral_excess p (hΦm _ _) (hXi 0)).eventually
    (gt_mem_nhds (half_pos hδ))).exists
  set ε := δ / 2 / ((d + 1) * B + 1)
  have hε : 0 < ε := by positivity
  have h2 : ε * ((d + 1) * B + 1) = δ / 2 := div_mul_cancel₀ _ (by positivity)
  have h3 : ε * (d + 1) * B = ε * ((d + 1) * B + 1) - ε := by ring
  have := step1 ε hε K
  linarith

end Energy

section Positivity

theorem infiniteComponentEvent_translation_iff (z : Vertex d) (ω : Configuration d)
    (x : Vertex d) :
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

theorem measure_infiniteComponentEvent_eq (p : unitInterval) (x : Vertex d) :
    latticeBondLaw d p (infiniteComponentEvent x) =
      latticeBondLaw d p (infiniteComponentEvent 0) := by
  have hpre : configurationTranslation (-x) ⁻¹' infiniteComponentEvent 0 =
      infiniteComponentEvent x := by
    ext ω
    simp only [Set.mem_preimage, infiniteComponentEvent_translation_iff, zero_sub, neg_neg]
  rw [← hpre, (measurePreserving_configurationTranslation p (-x)).measure_preimage
    (measurableSet_infiniteComponentEvent 0).nullMeasurableSet]

variable [NeZero d]

/-- **The corrected plane is not constant.** The gradients `X_k` do not all vanish almost
surely: otherwise `ℓ_{e₁}` would be constant on the cluster, while with positive probability
`n e₁ ∈ C_∞` for infinitely many `n` and `ℓ_{e₁}(n e₁) = n + o(n)`. -/
theorem not_forall_ae_eq_zero (p : unitInterval) {G : Set (Configuration d)}
    {Φ : Vertex d → Vertex d → Configuration d → ℝ}
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G)
    (hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ z, configurationTranslation z ω ∈ G)
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 d) u)
    (hΦ : IsEdgeField G Φ) :
    ¬ ∀ k : Fin d, ∀ᵐ ω ∂latticeBondLaw d p, Φ (unit k) 0 ω = 0 := by
  intro hzero
  set μ := latticeBondLaw d p
  have hz : ∀ᵐ ω ∂μ, ∀ z : Vertex d, ∀ k : Fin d,
      Φ (unit k) 0 (configurationTranslation z ω) = 0 :=
    ae_all_iff.2 fun z => ae_all_iff.2 fun k =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae (hzero k)
  set I : ℕ → Set (Configuration d) := fun n =>
    infiniteComponentEvent (((n : ℤ) • unit 0 : Vertex d))
  have hθ : μ (infiniteComponentEvent 0) ≠ 0 := by
    intro h0
    have hnull : μ (⋃ x : Vertex d, infiniteComponentEvent x) = 0 :=
      measure_iUnion_null fun x => by rw [measure_infiniteComponentEvent_eq]; exact h0
    have h1 : ∀ᵐ ω ∂μ, ω ∈ ⋃ x : Vertex d, infiniteComponentEvent x := by
      filter_upwards [hGae] with ω hω
      obtain ⟨h, -⟩ := hex ω hω
      obtain ⟨x, hx⟩ := (uniqueInfiniteComponent_infinite h).nonempty
      refine Set.mem_iUnion.2 ⟨x, ?_⟩
      change ((openGraph ω).connectedComponentMk x).supp.Infinite
      rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx]
      exact uniqueInfiniteComponent_infinite h
    obtain ⟨ω, hω1, hω2⟩ := (h1.and (measure_eq_zero_iff_ae_notMem.1 hnull)).exists
    exact hω2 hω1
  set B : ℕ → Set (Configuration d) := fun R => ⋃ n, ⋃ (_ : R ≤ n), I n
  have hBm : ∀ R, MeasurableSet (B R) := fun R =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      measurableSet_infiniteComponentEvent _
  have hBanti : Antitone B := fun R R' hRR' ω hω => by
    obtain ⟨n, hn, h⟩ := Set.mem_iUnion₂.1 hω
    exact Set.mem_iUnion₂.2 ⟨n, hRR'.trans hn, h⟩
  have hBge : ∀ R, μ (infiniteComponentEvent 0) ≤ μ (B R) := fun R => by
    rw [← measure_infiniteComponentEvent_eq p ((R : ℤ) • unit 0)]
    exact measure_mono fun ω h => Set.mem_iUnion₂.2 ⟨R, le_rfl, h⟩
  have hlim := tendsto_measure_iInter_atTop (fun R => (hBm R).nullMeasurableSet) hBanti
    ⟨0, measure_ne_top μ _⟩
  have hL : μ (⋂ R, B R) ≠ 0 := fun h =>
    hθ (le_antisymm (h ▸ ge_of_tendsto' hlim hBge) zero_le)
  apply hL
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hall, hz] with ω hω hzω hmem
  have hω0 : ω ∈ G := by simpa [configurationTranslation_zero] using hω 0
  obtain ⟨h, hexu⟩ := hex ω hω0
  have hC := uniqueInfiniteComponent_infinite h
  obtain ⟨u, hu⟩ := hexu _ hC
  have hedge : ∀ x y, x ∈ (uniqueInfiniteComponent h).supp → (openGraph ω).Adj x y →
      extend (uniqueInfiniteComponent h) u x = extend (uniqueInfiniteComponent h) u y := by
    intro x y hx hxy
    have hD : edgeDifference (uniqueInfiniteComponent h) u x y = 0 := by
      obtain ⟨k, hk | hk⟩ := Graph.Zd.adj_iff.1 hxy.1
      · subst hk
        rw [edgeDifference_antisymm _ u (x + unit k) x,
          edgeDifference_add_unit hΦ hω _ hC u hu x k, hzω, neg_zero]
      · subst hk
        have := edgeDifference_add_unit hΦ hω _ hC u hu (x - unit k) k
        rw [sub_add_cancel] at this
        rw [this, hzω]
    unfold edgeDifference at hD
    rw [if_pos ⟨hx, hxy⟩] at hD
    linarith
  have hwalk : ∀ (x y : Vertex d) (q : (openGraph ω).Walk x y),
      x ∈ (uniqueInfiniteComponent h).supp →
        extend (uniqueInfiniteComponent h) u x = extend (uniqueInfiniteComponent h) u y := by
    intro x y q
    induction q with
    | nil => exact fun _ => rfl
    | cons hadj q ih =>
      exact fun hx => (hedge _ _ hx hadj).trans
        (ih ((uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hx hadj))
  obtain ⟨x₀, hx₀⟩ := hC.nonempty
  set c := extend (uniqueInfiniteComponent h) u x₀
  obtain ⟨R₀, -, hR⟩ := hu.2 (1 / 4) (by norm_num)
  obtain ⟨R, hR1⟩ := exists_nat_ge (max R₀ (4 * |c| + 4))
  obtain ⟨n, hRn, hIn⟩ := Set.mem_iUnion₂.1 (Set.mem_iInter.1 hmem R)
  have hn : (R : ℝ) ≤ n := by exact_mod_cast hRn
  set y : Vertex d := (n : ℤ) • unit 0
  have hy : y ∈ (uniqueInfiniteComponent h).supp := by
    have hinf : ((openGraph ω).connectedComponentMk y).supp.Infinite := hIn
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, (eq_uniqueInfiniteComponent_iff h _).2 hinf]
  have hreach : (openGraph ω).Reachable x₀ y := by
    apply SimpleGraph.ConnectedComponent.exact
    rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx₀,
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy]
  obtain ⟨q⟩ := hreach
  have hcy : extend (uniqueInfiniteComponent h) u y = c := (hwalk _ _ q hx₀).symm
  have hy0 : ((y 0 : ℤ) : ℝ) = n := by simp [y, unit]
  have hdist : dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex d)) <
      n + 1 := by
    refine (dist_latticeEuclideanEmbedding_zero_le y).trans_lt ?_
    have : ∑ j, |((y j : ℤ) : ℝ)| = n := by
      rw [Finset.sum_eq_single (0 : Fin d) (fun j _ hj => by simp [y, unit, hj]) (by simp), hy0,
        abs_of_nonneg (Nat.cast_nonneg _)]
    rw [this]
    exact lt_add_one _
  have h4 := le_max_left R₀ (4 * |c| + 4)
  have h5 := le_max_right R₀ (4 * |c| + 4)
  have hb := hR (n + 1) (by linarith) ⟨y, hy⟩ ((mem_componentEuclideanBall _ 0 _ _).2 hdist)
  rw [componentSlope_slopeE1] at hb
  have hu' : u ⟨y, hy⟩ = c := by
    rw [← hcy]
    exact (dif_pos hy : Rigidity.Section3.extend (uniqueInfiniteComponent h) u y = _).symm
  simp only at hb
  rw [hu', hy0] at hb
  have := neg_abs_le (c - n)
  have := le_abs_self c
  linarith

end Positivity

section Main

/-- **Positivity of the homogenized coefficient**, from the box energy inequality. -/
theorem homogenizedCoefficientProposed_of_boxEnergy (hU : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput) (hQ : Rigidity.External.CorrectorQuantitativeInput)
    (hE : ∀ (d : ℕ) [NeZero d], BoxEnergyInequality d) : HomogenizedCoefficientProposed := by
  intro d _ hd p hpc hp1
  set μ := latticeBondLaw d p
  obtain ⟨G, hG, hG1, Φ, hΦm, hex, hΦ⟩ := exists_edgeField hU hCorr hd p hpc hp1
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := mem_ae_iff.2 ((prob_compl_eq_zero_iff hG).2 hG1)
  have hall : ∀ᵐ ω ∂μ, ∀ z, configurationTranslation z ω ∈ G :=
    ae_all_iff.2 fun z =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae hGae
  have hXi := fun k => integrable_edgeField_unit hQ hd p hpc hp1 hGae hΦm hex hΦ k
  have hge := integral_ge_energy (hE d) p hall hΦm hex hΦ hXi zero_le_one
  have iMin : ∀ k, Integrable (fun ω => min (Φ (unit k) 0 ω ^ 2) 1) μ := fun k =>
    (integrable_const (1 : ℝ)).mono'
      ((((hΦm _ _).pow_const 2).min measurable_const).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) zero_le_one)]
        exact min_le_right _ _)
  have hnn : ∀ k, 0 ≤ ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ := fun k =>
    integral_nonneg fun ω => le_min (sq_nonneg _) zero_le_one
  have hpos : 0 < ∑ k, ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ := by
    by_contra hle
    rw [not_lt] at hle
    apply not_forall_ae_eq_zero p hGae hall hex hΦ
    intro k
    have h0 : ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ = 0 := le_antisymm
      ((Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ k)).trans hle) (hnn k)
    rw [integral_eq_zero_iff_of_nonneg (fun ω => le_min (sq_nonneg _) zero_le_one) (iMin k)]
      at h0
    filter_upwards [h0] with ω hω
    by_contra hne
    have h1 : 0 < Φ (unit k) 0 ω ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    exact (lt_min h1 one_pos).ne' hω
  refine ⟨∫ ω, Φ (unit 0) 0 ω ∂μ, hpos.trans_le hge, fun X hX => ?_⟩
  have hXeq : X =ᵐ[μ] Φ (unit 0) 0 := by
    filter_upwards [hGae, hX] with ω hω hXω
    obtain ⟨h, hexu⟩ := hex ω hω
    obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
    rw [hXω h u hu]
    exact hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu _ _
  exact ⟨(hXi 0).congr hXeq.symm, integral_congr_ae hXeq⟩

end Main

section BoxEnergy

/-- **The box energy inequality holds** (`EnergyIdentity.lean`): `boxEnergy_eq` with the plane
deviation `ℓ - x₁ - c` as test function, and `abs_boundaryTerm_le`. -/
theorem boxEnergyInequality (d : ℕ) [NeZero d] : BoxEnergyInequality d := by
  intro ω C u hu N c η hosc
  have hE := boxEnergy_eq C u hu (latticeCube d N) c
  have hB := abs_boundaryTerm_le C u (latticeCube d N) (planeDeviation C u c) (M := η)
    (fun x hx hxC => by
      have := hosc ⟨x, hxC⟩ hx
      unfold planeDeviation
      rwa [show Rigidity.Section3.extend C u x = u ⟨x, hxC⟩ from dif_pos hxC])
  have h1 : boxEnergy C u (latticeCube d N) = ∑ k : Fin d,
      ∑ x ∈ (latticeCube d N).filter (fun x => x + unit k ∈ latticeCube d N),
        edgeDifference C u (x + unit k) x ^ 2 := by
    unfold boxEnergy
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · rw [edgeDifference_antisymm C u (x + unit k) x, neg_sq]
    · rfl
  have h2 : boxDrift C u (latticeCube d N) =
      ∑ x ∈ (latticeCube d N).filter (fun x => x + unit 0 ∈ latticeCube d N),
        edgeDifference C u (x + unit 0) x := by
    unfold boxDrift
    rw [Finset.sum_filter]
  have h3 : boundaryFlux C u (latticeCube d N) = ∑ k : Fin d,
      (∑ x ∈ (latticeCube d N).filter (fun x => x + unit k ∉ latticeCube d N),
          |edgeDifference C u x (x + unit k)| +
        ∑ x ∈ (latticeCube d N).filter (fun x => x - unit k ∉ latticeCube d N),
          |edgeDifference C u x (x - unit k)|) := by
    unfold boundaryFlux
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ite_not]
  rw [← h1, ← h2, ← h3]
  have := neg_abs_le (boundaryTerm C u (latticeCube d N) (planeDeviation C u c))
  linarith

end BoxEnergy

/-- **Positivity of the homogenized coefficient** (`HomogenizedCoefficientProposed`), from the
uniqueness of the infinite cluster, the existence of the corrected planes and Theorem 2.5. -/
theorem homogenizedCoefficientProposed (hU : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput) (hQ : Rigidity.External.CorrectorQuantitativeInput) :
    HomogenizedCoefficientProposed :=
  homogenizedCoefficientProposed_of_boxEnergy hU hCorr hQ fun d _ => boxEnergyInequality d

end HomogenizedCoefficient

end Rigidity.Proofs.S3
