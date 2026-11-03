import Rigidity.Steps.S3.NotLipschitz
import Rigidity.Proofs.S3.Reflection
import Rigidity.External.CorrectorQuantitative
import LatticeProb.Prob.Percolation.MeasurableCorrectorGradients
import LatticeProb.Prob.Birkhoff
import LatticeProb.Prob.Percolation.LatticeBondErgodicity

/-!
# Proposition 3.2: the flux of the corrected plane through the faces of `L(Q_N)`

Step `FluxEventStep` of Proposition 3.2 (`step:3.2-event`, eqs. (left-side-large) and
(other-sides-small), corrected draft L943-982). With probability tending to one, the corrected
plane `ℓ_{e₁}` has flux at least `(ā/2) N^{d-1}` out of `L(Q_N)` through `left(Q_N)` (over the
outward edges `(x, x - e₁)`, printed issue 1 of the carving) and at most `ε N^{d-1}` through
`sides(Q_N)`.

* **The field of edge differences.** On a measurable conull set `G` of configurations where the
  corrector clauses hold (`exists_measurable_corrector_valid_set`), the edge differences of every
  corrected plane of slope `e₁` on the infinite cluster are given by a measurable field `Φ`
  (`exists_measurable_corrector_gradients_on_valid_set`). Translations move the infinite cluster
  and its corrected planes (`isCorrectedPlane_translation_iff`), so on the conull set of
  configurations all of whose translates lie in `G`, the edge difference along `(x + w, y + w)`
  is `Φ(x, y)` at the configuration translated by `-w` (`edgeDifference_add_eq`).
* **The means.** The flux density through `left(Q_N)` is the edge difference
  `X = ℓ_{e₁}(e₁) - ℓ_{e₁}(0)` along `(e₁, 0)`, whose mean is the homogenized coefficient `ā > 0`
  (`HomogenizedCoefficientProposed`, proved in `Rigidity/Proofs/S3/HomogenizedCoefficient.lean`).
  Through the side `x_j = ±N`
  it is `±Y_j`, with `Y_j = ℓ_{e₁}(0) - ℓ_{e₁}(e_j)`; `Y_j` is integrable since the quantitative
  sublinearity of Theorem 2.5 (`CorrectorQuantitativeInput`) bounds it by `C (M + 2)` for a
  minimal scale `M ≤ O_s(C)`, and the reflection `x_j ↦ -x_j`, which preserves the law and the
  slope `e₁` (`step:3.1-reflection`), gives `Y_j ∘ R = -Y_j ∘ τ_{e_j}` almost surely, hence
  `E[Y_j] = 0`.
* **The ergodic theorem.** Each face is a segment of length `→ ∞` in one coordinate direction `k`
  over its slice, so the face average of `Z ∘ τ` is an average over the slice of the Birkhoff
  averages of `Z` along the ergodic translation `τ_{-e_k}` (`ergodic_configurationTranslation`);
  the `L¹` mean ergodic theorem (`tendsto_integral_abs_bAvg_sub`, from Birkhoff's pointwise
  theorem by truncation) and Markov's inequality give convergence in probability of the face
  averages to the means.

No literature input is used beyond the hypotheses of `fluxEventStep`: the uniqueness of the
infinite cluster and the existence of the corrected planes (Lattice-Probability), Theorem 2.5,
and the positivity of the homogenized coefficient. The last is not a literature input: it is
proved from the first three (`homogenizedCoefficientProposed hU hCorr hQ`,
`Rigidity/Proofs/S3/HomogenizedCoefficient.lean`, which imports this file), so `FluxEventStep`
holds from the literature inputs alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation LatticeProb.External
  Rigidity.Section3 Rigidity.Steps.S3

namespace Rigidity.Proofs.S3

/-- **Positivity of the homogenized coefficient** `ā > 0`: the gradient of the corrected plane
`ℓ_{e₁}` along the open edge `(e₁, 0)` of the infinite cluster is integrable, with mean `ā > 0`.

This is a theorem of the project, not an input: `homogenizedCoefficientProposed hU hCorr hQ`
(`Rigidity/Proofs/S3/HomogenizedCoefficient.lean`) proves it from the uniqueness of the infinite
cluster, the existence of the corrected planes and Theorem 2.5 (`CorrectorQuantitativeInput`).
Classical references for
`ā > 0`: Berger-Biskup 2007, Thm 3.2 (corrector); Armstrong-Dario 2018 and
Armstrong-Kuusi-Mourrat (homogenized coefficient). -/
def HomogenizedCoefficientProposed : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∃ abar > 0, ∀ X : Configuration d → ℝ,
      (∀ᵐ ω ∂latticeBondLaw d p, ∀ (h : HasUniqueInfiniteOpenComponent ω) u, IsCorrectedPlane (uniqueInfiniteComponent h)
        (slopeE1 d) u → X ω = edgeDifference (uniqueInfiniteComponent h) u (unit 0) 0) →
      Integrable X (latticeBondLaw d p) ∧ ∫ ω, X ω ∂latticeBondLaw d p = abar

namespace FluxEvent

/-! ### The `L¹` mean ergodic theorem -/

section Ergodic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}


/-- Integrals are invariant under a measure-preserving map. -/
theorem integral_comp_mp {σ : Ω → Ω} (hσ : MeasurePreserving σ μ μ) {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ) : ∫ x, g (σ x) ∂μ = ∫ x, g x ∂μ := by
  have h := integral_map (μ := μ) hσ.aemeasurable (φ := σ) (f := g)
    (by rw [hσ.map_eq]; exact hg)
  rw [hσ.map_eq] at h
  exact h.symm

theorem integrable_bAvg {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {u : Ω → ℝ}
    (hu : Integrable u μ) (n : ℕ) : Integrable (LatticeProb.bAvg T u n) μ := by
  unfold LatticeProb.bAvg birkhoffSum
  exact (integrable_finsetSum _ fun k _ =>
    (hT.iterate k).integrable_comp_of_integrable hu).div_const _

theorem integral_bAvg [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {u : Ω → ℝ} (hu : Integrable u μ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, LatticeProb.bAvg T u n x ∂μ = ∫ x, u x ∂μ := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : ∀ k ∈ Finset.range n, Integrable (fun x => u (T^[k] x)) μ := fun k _ =>
    (hT.iterate k).integrable_comp_of_integrable hu
  unfold LatticeProb.bAvg birkhoffSum
  rw [integral_div, integral_finsetSum _ hterm]
  rw [Finset.sum_congr rfl
    (fun k _ => integral_comp_mp (hT.iterate k) hu.aestronglyMeasurable)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hn0]

omit [MeasurableSpace Ω] in
theorem abs_bAvg_le_bAvg_abs (T : Ω → Ω) (u : Ω → ℝ) (n : ℕ) (x : Ω) :
    |LatticeProb.bAvg T u n x| ≤ LatticeProb.bAvg T (fun y => |u y|) n x := by
  unfold LatticeProb.bAvg birkhoffSum
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg n)

omit [MeasurableSpace Ω] in
theorem bAvg_sub (T : Ω → Ω) (u v : Ω → ℝ) (n : ℕ) (x : Ω) :
    LatticeProb.bAvg T (fun y => u y - v y) n x
      = LatticeProb.bAvg T u n x - LatticeProb.bAvg T v n x := by
  unfold LatticeProb.bAvg birkhoffSum
  rw [Finset.sum_sub_distrib, sub_div]

/-- The bounded case of the L¹ mean ergodic theorem. -/
theorem tendsto_integral_abs_bAvg_sub_of_bounded [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (hE : Ergodic T μ) {h : Ω → ℝ} (hhm : Measurable h)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M) :
    Tendsto (fun n : ℕ => ∫ x, |LatticeProb.bAvg T h n x - ∫ y, h y ∂μ| ∂μ) atTop (𝓝 0) := by
  have hInt : Integrable h μ :=
    Integrable.of_bound hhm.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa using hb x)
  have hae := LatticeProb.ae_tendsto_bLimsup hT hhm hInt
  have hinv := LatticeProb.ae_bLimsup_comp hT hhm hInt
  obtain ⟨c, hc⟩ := hE.ae_eq_const_of_ae_eq_comp₀
    (LatticeProb.measurable_bLimsup hT.measurable hhm).nullMeasurable hinv
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => |LatticeProb.bAvg T h n x - c|) atTop (𝓝 0) := by
    filter_upwards [hae, hc] with x hx hxc
    have hx' : Tendsto (fun n => LatticeProb.bAvg T h n x) atTop (𝓝 c) := by
      rw [hxc] at hx
      exact hx
    simpa using (hx'.sub_const c).abs
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x => |LatticeProb.bAvg T h n x - c|) μ :=
    fun n => ((LatticeProb.measurable_bAvg hT.measurable hhm n).sub_const c).abs.aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂μ, ‖|LatticeProb.bAvg T h n x - c|‖ ≤ M + |c| := by
    intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    calc |LatticeProb.bAvg T h n x - c| ≤ |LatticeProb.bAvg T h n x| + |c| := abs_sub _ _
      _ ≤ M + |c| := by
        have := LatticeProb.abs_bAvg_le (T := T) hM hb n x
        linarith
  have hD := tendsto_integral_of_dominated_convergence (fun _ => M + |c|) hmeas
    (integrable_const _) hbound hlim
  simp only [integral_zero] at hD
  have hceq : c = ∫ y, h y ∂μ := by
    have hle : ∀ n : ℕ, 1 ≤ n →
        |(∫ y, h y ∂μ) - c| ≤ ∫ x, |LatticeProb.bAvg T h n x - c| ∂μ := by
      intro n hn
      have hI : Integrable (LatticeProb.bAvg T h n) μ := integrable_bAvg hT hInt n
      calc |(∫ y, h y ∂μ) - c| = |∫ x, (LatticeProb.bAvg T h n x - c) ∂μ| := by
            rw [integral_sub hI (integrable_const c), integral_bAvg hT hInt hn]
            simp
        _ ≤ _ := abs_integral_le_integral_abs
    have h0 : |(∫ y, h y ∂μ) - c| ≤ 0 :=
      ge_of_tendsto hD (eventually_atTop.2 ⟨1, hle⟩)
    have h1 := abs_nonpos_iff.1 h0
    linarith
  rw [← hceq]
  exact hD

/-- L¹ mean ergodic theorem for one ergodic measure-preserving map. -/
theorem tendsto_integral_abs_bAvg_sub [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (hE : Ergodic T μ) {f : Ω → ℝ} (hfm : Measurable f)
    (hf : Integrable f μ) :
    Tendsto (fun n : ℕ => ∫ x, |LatticeProb.bAvg T f n x - ∫ y, f y ∂μ| ∂μ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∫ x, |f x - LatticeProb.clip (k : ℝ) f x| ∂μ < ε / 3 := by
    have := LatticeProb.tendsto_integral_abs_sub_clip hfm hf
    exact (this.eventually (gt_mem_nhds (by positivity))).exists
  have hgm : Measurable (LatticeProb.clip (k : ℝ) f) := LatticeProb.measurable_clip _ hfm
  have hgb : ∀ x, |LatticeProb.clip (k : ℝ) f x| ≤ (k : ℝ) :=
    fun x => LatticeProb.abs_clip_le (Nat.cast_nonneg k) x
  have hgI : Integrable (LatticeProb.clip (k : ℝ) f) μ :=
    Integrable.of_bound hgm.aestronglyMeasurable k
      (Eventually.of_forall fun x => by simpa using hgb x)
  have hB := tendsto_integral_abs_bAvg_sub_of_bounded hT hE hgm (Nat.cast_nonneg k) hgb
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hB (ε / 3) (by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have h1 := hN n hnN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  set g := LatticeProb.clip (k : ℝ) f with hg
  have hdI : Integrable (fun x => |f x - g x|) μ := (hf.sub hgI).abs
  have hI1 : Integrable (LatticeProb.bAvg T (fun y => |f y - g y|) n) μ :=
    integrable_bAvg hT hdI n
  have hI2 : Integrable (fun x => |LatticeProb.bAvg T g n x - ∫ y, g y ∂μ|) μ :=
    ((integrable_bAvg hT hgI n).sub (integrable_const _)).abs
  have hI12 : Integrable (fun x => LatticeProb.bAvg T (fun y => |f y - g y|) n x
      + |LatticeProb.bAvg T g n x - ∫ y, g y ∂μ|) μ := hI1.add hI2
  have hC : |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| ≤ ∫ x, |f x - g x| ∂μ := by
    calc |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| = |∫ x, (f x - g x) ∂μ| := by
          rw [integral_sub hf hgI, ← abs_neg, neg_sub]
      _ ≤ _ := abs_integral_le_integral_abs
  have hpoint : ∀ x, |LatticeProb.bAvg T f n x - ∫ y, f y ∂μ|
      ≤ (LatticeProb.bAvg T (fun y => |f y - g y|) n x
        + |LatticeProb.bAvg T g n x - ∫ y, g y ∂μ|) + |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| := by
    intro x
    have hdec : LatticeProb.bAvg T f n x - ∫ y, f y ∂μ
        = (LatticeProb.bAvg T (fun y => f y - g y) n x
          + (LatticeProb.bAvg T g n x - ∫ y, g y ∂μ)) + ((∫ y, g y ∂μ) - ∫ y, f y ∂μ) := by
      rw [bAvg_sub]
      ring
    have hA := abs_bAvg_le_bAvg_abs T (fun y => f y - g y) n x
    rw [hdec]
    calc _ ≤ |LatticeProb.bAvg T (fun y => f y - g y) n x
            + (LatticeProb.bAvg T g n x - ∫ y, g y ∂μ)|
          + |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| := abs_add_le _ _
      _ ≤ (|LatticeProb.bAvg T (fun y => f y - g y) n x|
            + |LatticeProb.bAvg T g n x - ∫ y, g y ∂μ|)
          + |(∫ y, g y ∂μ) - ∫ y, f y ∂μ| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by gcongr
  have hint : ∫ x, |LatticeProb.bAvg T f n x - ∫ y, f y ∂μ| ∂μ
      ≤ ∫ x, ((LatticeProb.bAvg T (fun y => |f y - g y|) n x
        + |LatticeProb.bAvg T g n x - ∫ y, g y ∂μ|)
        + |(∫ y, g y ∂μ) - ∫ y, f y ∂μ|) ∂μ :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (hI12.add (integrable_const _)) (Eventually.of_forall hpoint)
  rw [integral_add hI12 (integrable_const _), integral_add hI1 hI2,
    integral_bAvg hT hdI hn1] at hint
  simp only [integral_const, probReal_univ, one_smul] at hint
  linarith

/-- Averaging translates does not increase the L¹ distance to a constant. -/
theorem integral_abs_finsetAvg_sub_le [IsProbabilityMeasure μ] {ι : Type*} (S : Finset ι)
    (hS : S.Nonempty) {σ : ι → Ω → Ω} (hσ : ∀ i, MeasurePreserving (σ i) μ μ) {g : Ω → ℝ}
    (hgm : Measurable g) (hg : Integrable g μ) (c : ℝ) :
    ∫ x, |(∑ i ∈ S, g (σ i x)) / S.card - c| ∂μ ≤ ∫ x, |g x - c| ∂μ := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hterm : ∀ i ∈ S, Integrable (fun x => |g (σ i x) - c|) μ := fun i _ =>
    (((hσ i).integrable_comp_of_integrable hg).sub (integrable_const c)).abs
  have hpt : ∀ x, |(∑ i ∈ S, g (σ i x)) / S.card - c|
      ≤ (∑ i ∈ S, |g (σ i x) - c|) / S.card := by
    intro x
    have hdec : (∑ i ∈ S, g (σ i x)) / S.card - c
        = (∑ i ∈ S, (g (σ i x) - c)) / S.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [hdec, abs_div, abs_of_pos hcard]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcard.le
  calc ∫ x, |(∑ i ∈ S, g (σ i x)) / S.card - c| ∂μ
      ≤ ∫ x, (∑ i ∈ S, |g (σ i x) - c|) / S.card ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((integrable_finsetSum _ hterm).div_const _) (Eventually.of_forall hpt)
    _ = (∑ i ∈ S, ∫ x, |g (σ i x) - c| ∂μ) / S.card := by
        rw [integral_div, integral_finsetSum _ hterm]
    _ = (∑ i ∈ S, ∫ x, |g x - c| ∂μ) / S.card := by
        congr 1
        exact Finset.sum_congr rfl fun i _ =>
          integral_comp_mp (g := fun x => |g x - c|) (hσ i)
            (hgm.sub_const c).abs.aestronglyMeasurable
    _ = ∫ x, |g x - c| ∂μ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp


end Ergodic

/-! ### Stretched exponential moments and lattice boxes -/

variable {d : ℕ}


theorem le_one_add_factorial_mul_exp_rpow (t s : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (hn : 1 ≤ s * n) : t ≤ 1 + (n.factorial : ℝ) * Real.exp (Real.rpow t s) := by
  have hpos : 0 ≤ (n.factorial : ℝ) * Real.exp (Real.rpow t s) := by positivity
  by_cases h1 : t ≤ 1
  · linarith
  · push Not at h1
    have h2 : t ≤ t ^ (s * (n : ℝ)) := by
      calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ ≤ t ^ (s * (n : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1.le hn
    have h3 : t ^ (s * (n : ℝ)) = (Real.rpow t s) ^ n := by
      rw [Real.rpow_mul ht, Real.rpow_natCast]; rfl
    have h4 := Real.pow_div_factorial_le_exp (Real.rpow t s)
      (Real.rpow_nonneg ht s) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [div_le_iff₀ hf] at h4
    have h5 : (Real.rpow t s) ^ n ≤ (n.factorial : ℝ) * Real.exp (Real.rpow t s) := by
      linarith
    linarith

/-- A nonnegative variable with stretched exponential moments `M ≤ O_s(C)` is integrable. -/
theorem integrable_of_isOsBond {p : unitInterval} {M : Configuration d → ℝ} {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hM : Measurable M) (hM0 : ∀ ω, 0 ≤ M ω)
    (hOs : Rigidity.External.IsOsBond d p M s C) : Integrable M (latticeBondLaw d p) := by
  set n : ℕ := ⌈1 / s⌉₊ with hn
  have hn1 : 1 ≤ s * n := by
    have h1 : 1 / s ≤ n := Nat.le_ceil _
    rw [div_le_iff₀ hs] at h1
    linarith
  have hint : Integrable (fun ω => C * (1 + (n.factorial : ℝ) *
      Real.exp (Real.rpow (max (M ω / C) 0) s))) (latticeBondLaw d p) := by
    refine Integrable.const_mul ?_ C
    refine Integrable.add (integrable_const _) ?_
    exact hOs.1.const_mul _
  refine Integrable.mono' hint hM.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ M ω / C := div_nonneg (hM0 ω) hC.le
  have h1 := le_one_add_factorial_mul_exp_rpow (M ω / C) s h0 n hn1
  rw [Real.norm_of_nonneg (hM0 ω), max_eq_left h0]
  calc M ω = C * (M ω / C) := by field_simp
    _ ≤ C * (1 + (n.factorial : ℝ) * Real.exp (Real.rpow (M ω / C) s)) :=
        mul_le_mul_of_nonneg_left h1 hC.le

/-- A finite set of sites which is a segment `[a, b]` in direction `k` over its slice
`x k = a` splits as slice × segment. -/
theorem sum_eq_sum_slice (F : Finset (Vertex d)) (k : Fin d) (a b : ℤ) (hab : a ≤ b)
    (hF : ∀ x, x ∈ F ↔ a ≤ x k ∧ x k ≤ b ∧ Function.update x k a ∈ F) (φ : Vertex d → ℝ) :
    ∑ x ∈ F, φ x = ∑ s ∈ F.filter (fun x => x k = a),
      ∑ t ∈ Finset.range (b - a + 1).toNat, φ (s + (t : ℤ) • LatticeProb.unit k) := by
  have hab' : a ≤ b := hab
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (Function.update x k a, (x k - a).toNat))
    (fun q => q.1 + (q.2 : ℤ) • LatticeProb.unit k) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := (hF x).1 hx
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨h3, by simp⟩, ?_⟩
    omega
  · rintro ⟨s, t⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨hs, hsk⟩, ht⟩ := hq
    have hk : (s + (t : ℤ) • LatticeProb.unit k) k = a + t := by
      simp [LatticeProb.unit, hsk]
    have hu : Function.update (s + (t : ℤ) • LatticeProb.unit k) k a = s := by
      funext i
      by_cases hi : i = k
      · subst hi; simp [hsk]
      · simp [hi, LatticeProb.unit]
    rw [hF]
    refine ⟨by rw [hk]; omega, by rw [hk]; omega, by rw [hu]; exact hs⟩
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := (hF x).1 hx
    funext i
    by_cases hi : i = k
    · subst hi; simp [LatticeProb.unit]; omega
    · simp [hi, LatticeProb.unit]
  · rintro ⟨s, t⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨hs, hsk⟩, ht⟩ := hq
    have hk : (s + (t : ℤ) • LatticeProb.unit k) k = a + t := by
      simp [LatticeProb.unit, hsk]
    have hu : Function.update (s + (t : ℤ) • LatticeProb.unit k) k a = s := by
      funext i
      by_cases hi : i = k
      · subst hi; simp [hsk]
      · simp [hi, LatticeProb.unit]
    refine Prod.ext hu ?_
    show ((s + (t : ℤ) • LatticeProb.unit k) k - a).toNat = t
    rw [hk]; omega
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := (hF x).1 hx
    have : Function.update x k a + ((x k - a).toNat : ℤ) • LatticeProb.unit k = x := by
      funext i
      by_cases hi : i = k
      · subst hi; simp [LatticeProb.unit]; omega
      · simp [hi, LatticeProb.unit]
    simp only [this]

theorem card_eq_card_slice_mul (F : Finset (Vertex d)) (k : Fin d) (a b : ℤ) (hab : a ≤ b)
    (hF : ∀ x, x ∈ F ↔ a ≤ x k ∧ x k ≤ b ∧ Function.update x k a ∈ F) :
    F.card = (F.filter (fun x => x k = a)).card * (b - a + 1).toNat := by
  have h := sum_eq_sum_slice F k a b hab hF (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range] at h
  exact_mod_cast h

theorem card_latticeCube_filter_eq (N : ℕ) (i : Fin d) (c : ℤ) (hc1 : -(N : ℤ) ≤ c)
    (hc2 : c ≤ N) :
    ((Rigidity.Steps.S3.latticeCube d N).filter fun x => x i = c).card = (2 * N + 1) ^ (d - 1) := by
  have hset : (Rigidity.Steps.S3.latticeCube d N).filter (fun x => x i = c) =
      Fintype.piFinset (Function.update (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N) i {c}) := by
    ext x
    simp only [Finset.mem_filter, Rigidity.Steps.S3.latticeCube, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simp [h2]
      · simp [hj, h1 j]
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj
          have := h j
          simp at this
          simp [this, hc1, hc2]
        · simpa [hj] using h j
      · have := h i
        simpa using this
  have hcard : ∀ j : Fin d, (Function.update (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N) i {c} j).card =
      Function.update (fun _ : Fin d => 2 * N + 1) i 1 j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]; omega
  rw [hset, Fintype.card_piFinset]
  simp only [hcard]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.prod_const, Finset.card_sdiff]

/-! ### The faces of `L(Q_N)` -/

section Faces

theorem mem_latticeCube {N : ℕ} {x : Vertex d} :
    x ∈ latticeCube d N ↔ ∀ i, -(N : ℤ) ≤ x i ∧ x i ≤ N := by
  simp only [latticeCube, Fintype.mem_piFinset, Finset.mem_Icc]

theorem update_mem_latticeCube {N : ℕ} {x : Vertex d} {k : Fin d} :
    Function.update x k (-(N : ℤ)) ∈ latticeCube d N ↔
      ∀ i, i ≠ k → -(N : ℤ) ≤ x i ∧ x i ≤ N := by
  rw [mem_latticeCube]
  constructor
  · intro hx i hi
    simpa only [Function.update_of_ne hi] using hx i
  · intro hx i
    by_cases hi : i = k
    · subst hi
      simp only [Function.update_self]
      omega
    · simpa only [Function.update_of_ne hi] using hx i hi

variable [NeZero d]

/-- `left(Q_N)` is the segment `[-N, N]` in a direction `k ≠ 1` over its slice. -/
theorem mem_leftFace_iff (N : ℕ) {k : Fin d} (hk : k ≠ 0) (x : Vertex d) :
    x ∈ leftFace d N ↔
      -(N : ℤ) ≤ x k ∧ x k ≤ N ∧ Function.update x k (-(N : ℤ)) ∈ leftFace d N := by
  simp only [leftFace, Finset.mem_filter, update_mem_latticeCube]
  simp only [mem_latticeCube, Function.update_of_ne (Ne.symm hk)]
  constructor
  · rintro ⟨hx, h0⟩
    exact ⟨(hx k).1, (hx k).2, fun i _ => hx i, h0⟩
  · rintro ⟨h1, h2, hx, h0⟩
    refine ⟨fun i => ?_, h0⟩
    by_cases hi : i = k
    · subst hi
      exact ⟨h1, h2⟩
    · exact hx i hi

/-- The side `x_j = c` of `L(Q_N)` is the segment `[-N, 0]` in the direction `1` over its
slice. -/
theorem mem_side_iff (N : ℕ) {j : Fin d} (hj : j ≠ 0) (c : ℤ) (x : Vertex d) :
    x ∈ (halfCube d N).filter (fun x => x j = c) ↔
      -(N : ℤ) ≤ x 0 ∧ x 0 ≤ 0 ∧
        Function.update x 0 (-(N : ℤ)) ∈ (halfCube d N).filter (fun x => x j = c) := by
  simp only [halfCube, Finset.mem_filter, update_mem_latticeCube]
  simp only [mem_latticeCube, Function.update_self, Function.update_of_ne hj]
  constructor
  · rintro ⟨⟨hx, h0⟩, hc⟩
    exact ⟨(hx 0).1, h0, ⟨⟨fun i _ => hx i, by omega⟩, hc⟩⟩
  · rintro ⟨h1, h2, ⟨hx, -⟩, hc⟩
    refine ⟨⟨fun i => ?_, h2⟩, hc⟩
    by_cases hi : i = 0
    · subst hi
      exact ⟨h1, by omega⟩
    · exact hx i hi

theorem card_side_le (N : ℕ) (j : Fin d) (c : ℤ) (hc1 : -(N : ℤ) ≤ c) (hc2 : c ≤ N) :
    ((halfCube d N).filter (fun x => x j = c)).card ≤ (2 * N + 1) ^ (d - 1) := by
  rw [← card_latticeCube_filter_eq N j c hc1 hc2]
  refine Finset.card_le_card fun x hx => ?_
  simp only [halfCube, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1.1, hx.2⟩

end Faces

/-! ### Edge differences under the lattice symmetries -/

section EdgeDifference

variable {ω : Configuration d}

/-- The discrete normal derivative is antisymmetric. -/
theorem edgeDifference_comm (C : OpenComponent ω) (u : C → ℝ) (x y : Vertex d) :
    edgeDifference C u x y = -edgeDifference C u y x := by
  unfold edgeDifference
  by_cases hxy : (openGraph ω).Adj x y
  · by_cases hx : x ∈ C.supp
    · have hy : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hx hxy
      rw [if_pos ⟨hx, hxy⟩, if_pos ⟨hy, hxy.symm⟩, neg_sub]
    · have hy : y ∉ C.supp := fun hy => hx (C.mem_supp_of_adj_mem_supp hy hxy.symm)
      rw [if_neg fun h => hx h.1, if_neg fun h => hy h.1, neg_zero]
  · rw [if_neg fun h => hxy h.2, if_neg fun h => hxy h.2.symm, neg_zero]

/-- The extension by zero of a translated function. -/
theorem extend_translation (z : Vertex d) (C : OpenComponent ω) (u : C → ℝ) (x : Vertex d) :
    Rigidity.Section3.extend (openComponentTranslation z ω C)
        (fun y => u ((openComponentTranslationIso z C).symm y)) x = Rigidity.Section3.extend C u (x - z) := by
  unfold Rigidity.Section3.extend
  by_cases hx : x - z ∈ C.supp
  · have hx' : x ∈ (openComponentTranslation z ω C).supp :=
      (mem_openComponentTranslation_supp z C x).2 hx
    rw [dif_pos hx', dif_pos hx]
    exact congrArg u (Subtype.ext (openComponentTranslationIso_symm_val z C _))
  · have hx' : x ∉ (openComponentTranslation z ω C).supp :=
      fun h => hx ((mem_openComponentTranslation_supp z C x).1 h)
    rw [dif_neg hx', dif_neg hx]

/-- The discrete normal derivative of a translated function along an edge is the discrete normal
derivative along the translated edge. -/
theorem edgeDifference_translation (z : Vertex d) (C : OpenComponent ω) (u : C → ℝ)
    (x y : Vertex d) :
    edgeDifference (openComponentTranslation z ω C)
        (fun y => u ((openComponentTranslationIso z C).symm y)) x y =
      edgeDifference C u (x - z) (y - z) := by
  have hadj : (openGraph (configurationTranslation z ω)).Adj x y ↔
      (openGraph ω).Adj (x - z) (y - z) := by
    have := openGraph_adj_translation_iff z ω (x - z) (y - z)
    rwa [sub_add_cancel, sub_add_cancel] at this
  have hmem := mem_openComponentTranslation_supp z C x
  unfold edgeDifference
  simp only [extend_translation]
  by_cases hc : x - z ∈ C.supp ∧ (openGraph ω).Adj (x - z) (y - z)
  · rw [if_pos hc, if_pos ⟨hmem.2 hc.1, hadj.2 hc.2⟩]
  · rw [if_neg hc, if_neg fun h => hc ⟨hmem.1 h.1, hadj.1 h.2⟩]

variable (φ : nearestNeighborGraph d ≃g nearestNeighborGraph d)

/-- A lattice automorphism carries the support of a component onto the support of its image. -/
theorem mem_openComponentMap_supp (C : OpenComponent ω) (x : Vertex d) :
    φ x ∈ (openComponentMap φ ω C).supp ↔ x ∈ C.supp := by
  constructor
  · intro hx
    have hval : φ ((openComponentMapIso φ C).symm ⟨φ x, hx⟩).val = φ x :=
      congrArg Subtype.val ((openComponentMapIso φ C).apply_symm_apply ⟨φ x, hx⟩)
    exact φ.injective hval ▸ ((openComponentMapIso φ C).symm ⟨φ x, hx⟩).2
  · intro hx
    exact (openComponentMapIso φ C ⟨x, hx⟩).2

theorem extend_map (C : OpenComponent ω) (v : openComponentMap φ ω C → ℝ) (x : Vertex d) :
    Rigidity.Section3.extend C (fun y => v (openComponentMapIso φ C y)) x =
      Rigidity.Section3.extend (openComponentMap φ ω C) v (φ x) := by
  unfold Rigidity.Section3.extend
  by_cases hx : x ∈ C.supp
  · rw [dif_pos hx, dif_pos ((mem_openComponentMap_supp φ C x).2 hx)]
    rfl
  · rw [dif_neg hx, dif_neg fun h => hx ((mem_openComponentMap_supp φ C x).1 h)]

/-- The discrete normal derivative of a transported function along a transported edge. -/
theorem edgeDifference_map (C : OpenComponent ω) (v : openComponentMap φ ω C → ℝ)
    (x y : Vertex d) :
    edgeDifference (openComponentMap φ ω C) v (φ x) (φ y) =
      edgeDifference C (fun y => v (openComponentMapIso φ C y)) x y := by
  have hmem := mem_openComponentMap_supp φ C x
  have hadj := openGraph_adj_configurationMap_iff φ ω x y
  unfold edgeDifference
  simp only [extend_map]
  by_cases hc : x ∈ C.supp ∧ (openGraph ω).Adj x y
  · rw [if_pos hc, if_pos ⟨hmem.2 hc.1, hadj.2 hc.2⟩]
  · rw [if_neg hc, if_neg fun h => hc ⟨hmem.1 h.1, hadj.1 h.2⟩]

end EdgeDifference

/-! ### The field of edge differences of the corrected plane of slope `e₁` -/

section Field

variable [NeZero d]

/-- The edge differences of the corrected planes of slope `e₁` on an infinite cluster are the
values of `Φ`. -/
def IsEdgeField (G : Set (Configuration d)) (Φ : Vertex d → Vertex d → Configuration d → ℝ) :
    Prop :=
  ∀ ω ∈ G, ∀ C : OpenComponent ω, C.supp.Infinite → ∀ u, IsCorrectedPlane C (slopeE1 d) u →
    ∀ x y, edgeDifference C u x y = Φ x y ω

/-- **The measurable field of edge differences.** There are a measurable conull set `G` of
configurations with a unique infinite cluster carrying corrected planes of slope `e₁`, and a
measurable field `Φ` of the edge differences of these corrected planes on `G`. -/
theorem exists_edgeField (hU : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput) (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ G : Set (Configuration d), MeasurableSet G ∧ latticeBondLaw d p G = 1 ∧
      ∃ Φ : Vertex d → Vertex d → Configuration d → ℝ, (∀ x y, Measurable (Φ x y)) ∧
        (∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
          ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 d) u) ∧
        IsEdgeField G Φ := by
  classical
  obtain ⟨G, hG, hG1, hvalid⟩ := exists_measurable_corrector_valid_set hU hCorr d hd p hpc hp1
  obtain ⟨g, hgm, hzero, hgrad, -⟩ :=
    exists_measurable_corrector_gradients_on_valid_set G hG hvalid
  refine ⟨G, hG, hG1, fun x y ω => if hω : ω ∈ G then -g ⟨ω, hω⟩ (x, y) 0 else 0,
    fun x y => Measurable.dite (hgm (x, y) 0).neg (g := fun _ => (0 : ℝ)) measurable_const hG,
    fun ω hω => ⟨(hvalid hω).1, fun C hC => ?_⟩, fun ω hω C hC u hu x y => ?_⟩
  · have h := (hvalid hω).1
    obtain rfl := (eq_uniqueInfiniteComponent_iff h C).2 hC
    obtain ⟨o, ho⟩ := hC.nonempty
    obtain ⟨u, ⟨hu, -⟩, -⟩ := ((hvalid hω).2 h).1 (slopeE1 d) ⟨o, ho⟩
    exact ⟨u, hu⟩
  · have h := (hvalid hω).1
    obtain rfl := (eq_uniqueInfiniteComponent_iff h C).2 hC
    simp only [dif_pos hω]
    unfold edgeDifference
    split_ifs with hxy
    · have hy : y ∈ (uniqueInfiniteComponent h).supp :=
        (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hxy.1 hxy.2
      have hg := hgrad ⟨ω, hω⟩ (slopeE1 d) u hu ⟨x, hxy.1⟩ ⟨y, hy⟩ hxy.2
      have hsum : ∑ j, slopeE1 d j * g ⟨ω, hω⟩ (x, y) j = g ⟨ω, hω⟩ (x, y) 0 := by
        simp [slopeE1, Pi.single_apply]
      simp only [Rigidity.Section3.extend, dif_pos hxy.1, dif_pos hy]
      linarith
    · rw [hzero ⟨ω, hω⟩ (x, y) ?_ 0, neg_zero]
      rintro ⟨hinf, hadj⟩
      exact hxy ⟨(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        ((eq_uniqueInfiniteComponent_iff h _).2 hinf), hadj⟩

/-- **Stationarity of the edge differences.** On a configuration all of whose translates lie in
`G`, the edge difference along `(x + w, y + w)` is `Φ(x, y)` at the configuration translated by
`-w`. -/
theorem edgeDifference_add_eq {G : Set (Configuration d)}
    {Φ : Vertex d → Vertex d → Configuration d → ℝ} (hΦ : IsEdgeField G Φ)
    {ω : Configuration d} (hω : ∀ z, configurationTranslation z ω ∈ G) (C : OpenComponent ω)
    (hC : C.supp.Infinite) (u : C → ℝ) (hu : IsCorrectedPlane C (slopeE1 d) u) (x y w : Vertex d) :
    edgeDifference C u (x + w) (y + w) = Φ x y (configurationTranslation (-w) ω) := by
  have := hΦ _ (hω (-w)) (openComponentTranslation (-w) ω C)
    ((openComponentTranslation_infinite_iff (-w) C).2 hC)
    (fun y => u ((openComponentTranslationIso (-w) C).symm y))
    ((isCorrectedPlane_translation_iff (-w) C (slopeE1 d) u).2 hu) x y
  rwa [edgeDifference_translation, sub_neg_eq_add, sub_neg_eq_add] at this

omit [NeZero d] in
theorem norm_latticeEuclideanEmbedding_unit_sub_zero (j : Fin d) :
    ‖latticeEuclideanEmbedding (unit j : Vertex d) - latticeEuclideanEmbedding 0‖ ≤ 1 := by
  rw [← latticeEuclideanEmbedding_sub, sub_zero, EuclideanSpace.norm_eq]
  have hsq : ∀ i, ‖latticeEuclideanEmbedding (unit j : Vertex d) i‖ ^ 2 =
      if i = j then 1 else 0 := by
    intro i
    change ‖(((Pi.single j 1 : Vertex d) i : ℤ) : ℝ)‖ ^ 2 = _
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  simp only [hsq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Real.sqrt_one, le_refl]

/-- **Integrability of the side gradients** (Theorem 2.5 with `α = 1` at the origin): the edge
difference `Y_j = ℓ_{e₁}(0) - ℓ_{e₁}(e_j)`, `j ≠ 1`, is at most `C (M + 2)` for a minimal scale
`M ≤ O_s(C)`. -/
theorem integrable_sideField (hQ : Rigidity.External.CorrectorQuantitativeInput) (hd : 2 ≤ d)
    (p : unitInterval) (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {G : Set (Configuration d)} (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G)
    {Φ : Vertex d → Vertex d → Configuration d → ℝ} (hΦm : ∀ x y, Measurable (Φ x y))
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 d) u)
    (hΦ : IsEdgeField G Φ) {j : Fin d} (hj : j ≠ 0) :
    Integrable (Φ 0 (unit j)) (latticeBondLaw d p) := by
  obtain ⟨s, C, hs, hC, hM⟩ := hQ d hd p hpc hp1 1 one_pos
  obtain ⟨M, hMm, hM0, hMos, hbound⟩ := hM 0
  refine Integrable.mono' (((integrable_of_isOsBond hs hC hMm hM0 hMos).add
    (integrable_const 2)).const_mul C) (hΦm 0 (unit j)).aestronglyMeasurable ?_
  filter_upwards [hGae, hbound] with ω hω hb
  obtain ⟨h, hexu⟩ := hex ω hω
  obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
  rw [← hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu, Real.norm_eq_abs]
  have hr : 0 ≤ M ω + 2 := by linarith [hM0 ω]
  unfold edgeDifference
  split_ifs with h0
  · have hj' : unit j ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp h0.1 h0.2
    let a : uniqueInfiniteComponent h := ⟨0, h0.1⟩
    let b : uniqueInfiniteComponent h := ⟨unit j, hj'⟩
    have hna : ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding 0‖ < M ω + 2 := by
      simp only [a, sub_self, norm_zero]
      linarith [hM0 ω]
    have hnb : ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding 0‖ < M ω + 2 :=
      (norm_latticeEuclideanEmbedding_unit_sub_zero j).trans_lt (by linarith [hM0 ω])
    have hab : (componentGraph (uniqueInfiniteComponent h)).Adj a b :=
      ((uniqueInfiniteComponent h).toSimpleGraph_adj a.2 b.2).2 h0.2
    have hbd := hb h (slopeE1 d) u hu (M ω + 2) (by linarith) a a a b hna hna hna hnb hab
    have hqa : ∑ i, slopeE1 d i * ((a.val i : ℤ) : ℝ) = 0 := by simp [a]
    have hqb : ∑ i, slopeE1 d i * ((b.val i : ℤ) : ℝ) = 0 := by
      simp [b, slopeE1, unit, Pi.single_apply, hj]
    have hq : ∑ i, |slopeE1 d i| = 1 := by
      rw [Finset.sum_eq_single (0 : Fin d) (fun i _ hi => by simp [slopeE1, hi]) (by simp)]
      simp [slopeE1]
    rw [hqa, hqb, hq, sub_self, abs_zero, zero_add, Real.rpow_one, sub_zero, sub_zero,
      mul_one] at hbd
    have e0 : Rigidity.Section3.extend (uniqueInfiniteComponent h) u 0 = u a := dif_pos h0.1
    have ej : Rigidity.Section3.extend (uniqueInfiniteComponent h) u (unit j) = u b :=
      dif_pos hj'
    rw [e0, ej]
    exact hbd
  · rw [abs_zero]
    exact mul_nonneg hC.le hr

/-- **The side gradients have mean zero** (`step:3.1-reflection`): the reflection `R` of the
coordinate `j ≠ 1` preserves the law and the slope `e₁`, and `Y_j ∘ R = -Y_j ∘ τ_{e_j}`
almost surely. -/
theorem integral_sideField_eq_zero (p : unitInterval) {G : Set (Configuration d)}
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {Φ : Vertex d → Vertex d → Configuration d → ℝ}
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 d) u)
    (hΦ : IsEdgeField G Φ) {j : Fin d} (hj : j ≠ 0)
    (hY : Integrable (Φ 0 (unit j)) (latticeBondLaw d p)) :
    ∫ ω, Φ 0 (unit j) ω ∂latticeBondLaw d p = 0 := by
  set μ := latticeBondLaw d p
  set s : Fin d → ℤˣ := Function.update 1 j (-1)
  set R := signedPermIso (Equiv.refl (Fin d)) s
  have hR0 : R 0 = 0 := signedPermIso_zero _ _
  have hRj : R (-unit j) = unit j := by
    funext i
    change (s i : ℤ) * (-unit j) i = unit j i
    by_cases hij : i = j
    · subst hij
      simp [s, unit]
    · simp [s, unit, hij]
  have hslope : signedPermSlope (Equiv.refl (Fin d)) s (slopeE1 d) = slopeE1 d := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [signedPermSlope, slopeE1, s, Function.update_of_ne (Ne.symm hj)]
    · simp [signedPermSlope, slopeE1, s, hi]
  have hall : ∀ᵐ ω ∂μ, ∀ z, configurationTranslation z ω ∈ G :=
    ae_all_iff.2 fun z =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae hGae
  have hae : ∀ᵐ ω ∂μ, Φ 0 (unit j) (configurationMap R ω) =
      -Φ 0 (unit j) (configurationTranslation (unit j) ω) := by
    filter_upwards [hall, (measurePreserving_configurationMap R p).quasiMeasurePreserving.ae hGae]
      with ω hω hRω
    have hω0 : ω ∈ G := by simpa only [configurationTranslation_zero] using hω 0
    obtain ⟨h, -⟩ := hex ω hω0
    have hC₂ : (openComponentMap R ω (uniqueInfiniteComponent h)).supp.Infinite :=
      (openComponentMap_infinite_iff R _).2 (uniqueInfiniteComponent_infinite h)
    obtain ⟨v, hv⟩ := (hex _ hRω).2 _ hC₂
    have hu := isCorrectedPlane_comp_signedPerm (Equiv.refl (Fin d)) s
      (uniqueInfiniteComponent h) (slopeE1 d) v (by rwa [hslope])
    have e1 := hΦ _ hRω _ hC₂ v hv (R 0) (R (-unit j))
    rw [edgeDifference_map, hR0, hRj, edgeDifference_comm] at e1
    have e2 := edgeDifference_add_eq hΦ hω (uniqueInfiniteComponent h)
      (uniqueInfiniteComponent_infinite h) _ hu 0 (unit j) (-unit j)
    rw [zero_add, add_neg_cancel, neg_neg] at e2
    rw [← e1, e2]
  have h1 : ∫ ω, Φ 0 (unit j) ω ∂μ = ∫ ω, Φ 0 (unit j) (configurationMap R ω) ∂μ :=
    ((measurePreserving_configurationMap R p).integral_comp' _).symm
  have h2 : ∫ ω, Φ 0 (unit j) (configurationTranslation (unit j) ω) ∂μ =
      ∫ ω, Φ 0 (unit j) ω ∂μ :=
    integral_comp_mp (measurePreserving_configurationTranslation p (unit j))
      hY.aestronglyMeasurable
  rw [integral_congr_ae hae, integral_neg, h2] at h1
  linarith

end Field

/-! ### Face averages -/

section FaceAverage

/-- The average of `Z ∘ τ_{c - x}` over the sites `x` of a finite set `F`. -/
noncomputable def faceAverage (Z : Configuration d → ℝ) (F : Finset (Vertex d)) (c : Vertex d)
    (ω : Configuration d) : ℝ :=
  (∑ x ∈ F, Z (configurationTranslation (c - x) ω)) / F.card

theorem sum_eq_faceAverage_mul (Z : Configuration d → ℝ) {F : Finset (Vertex d)}
    (hF : F.Nonempty) (c : Vertex d) (ω : Configuration d) :
    ∑ x ∈ F, Z (configurationTranslation (c - x) ω) = faceAverage Z F c ω * F.card := by
  have : (F.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hF.card_pos.ne'
  rw [faceAverage, div_mul_cancel₀ _ this]

theorem iterate_configurationTranslation (v : Vertex d) (t : ℕ) (ω : Configuration d) :
    (⇑(configurationTranslation v))^[t] ω = configurationTranslation ((t : ℤ) • v) ω := by
  induction t with
  | zero => simp [configurationTranslation_zero]
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, configurationTranslation_add]
    congr 1
    push_cast
    rw [add_smul, one_smul, add_comm]

/-- **Convergence in probability of the face averages.** If the sets `F_N` are segments
`[a_N, b_N]` in a direction `k` over their slices, with `b_N - a_N → ∞`, then for integrable `Z`
the face averages of `Z ∘ τ` over `F_N` converge in probability to `E[Z]`. -/
theorem tendsto_measure_faceAverage [NeZero d] (p : unitInterval) {Z : Configuration d → ℝ}
    (hZm : Measurable Z) (hZ : Integrable Z (latticeBondLaw d p)) (k : Fin d)
    (F : ℕ → Finset (Vertex d)) (c : ℕ → Vertex d) (a b : ℕ → ℤ) (hab : ∀ N, a N ≤ b N)
    (hlen : Tendsto (fun N => (b N - a N + 1).toNat) atTop atTop)
    (hF : ∀ N x, x ∈ F N ↔ a N ≤ x k ∧ x k ≤ b N ∧ Function.update x k (a N) ∈ F N)
    (hne : ∀ N, (F N).Nonempty) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N => latticeBondLaw d p {ω | η ≤
      |faceAverage Z (F N) (c N) ω - ∫ ω', Z ω' ∂latticeBondLaw d p|}) atTop (𝓝 0) := by
  set μ := latticeBondLaw d p
  set T := ⇑(configurationTranslation (-unit k : Vertex d))
  have hT : MeasurePreserving T μ μ := measurePreserving_configurationTranslation p _
  have hE : Ergodic T μ := ergodic_configurationTranslation p (neg_ne_zero.2 (unit_ne_zero k))
  have hn : ∀ N, 1 ≤ (b N - a N + 1).toNat := fun N => by have := hab N; omega
  set S := fun N => (F N).filter (fun x => x k = a N)
  have hS : ∀ N, (S N).Nonempty := by
    intro N
    obtain ⟨x, hx⟩ := hne N
    exact ⟨Function.update x k (a N),
      Finset.mem_filter.2 ⟨((hF N x).1 hx).2.2, Function.update_self _ _ _⟩⟩
  have hid : ∀ N ω, faceAverage Z (F N) (c N) ω =
      (∑ s ∈ S N, LatticeProb.bAvg T Z (b N - a N + 1).toNat
        (configurationTranslation (c N - s) ω)) / (S N).card := by
    intro N ω
    have hn0 : ((b N - a N + 1).toNat : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hn N; omega)
    have hinner : ∀ s, ∑ t ∈ Finset.range (b N - a N + 1).toNat,
        Z (configurationTranslation (c N - (s + (t : ℤ) • unit k)) ω) =
          (b N - a N + 1).toNat * LatticeProb.bAvg T Z (b N - a N + 1).toNat
            (configurationTranslation (c N - s) ω) := by
      intro s
      rw [LatticeProb.bAvg, birkhoffSum, mul_div_cancel₀ _ hn0]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [iterate_configurationTranslation, configurationTranslation_add]
      congr 2
      rw [smul_neg]
      abel
    rw [faceAverage, sum_eq_sum_slice (F N) k (a N) (b N) (hab N) (hF N),
      card_eq_card_slice_mul (F N) k (a N) (b N) (hab N) (hF N)]
    simp_rw [hinner]
    rw [← Finset.mul_sum, Nat.cast_mul, mul_comm ((S N).card : ℝ), mul_div_mul_left _ _ hn0]
  have hbound : ∀ N, μ.real {ω | η ≤ |faceAverage Z (F N) (c N) ω - ∫ ω', Z ω' ∂μ|} ≤
      (∫ ω, |LatticeProb.bAvg T Z (b N - a N + 1).toNat ω - ∫ ω', Z ω' ∂μ| ∂μ) / η := by
    intro N
    have hint : Integrable (fun ω => |(∑ s ∈ S N, LatticeProb.bAvg T Z (b N - a N + 1).toNat
        (configurationTranslation (c N - s) ω)) / (S N).card - ∫ ω', Z ω' ∂μ|) μ :=
      (((integrable_finsetSum _ fun s _ =>
        (measurePreserving_configurationTranslation p (c N - s)).integrable_comp_of_integrable
          (integrable_bAvg hT hZ _)).div_const _).sub (integrable_const _)).abs
    rw [le_div_iff₀ hη, mul_comm]
    simp_rw [hid]
    calc η * μ.real {ω | η ≤ |(∑ s ∈ S N, LatticeProb.bAvg T Z (b N - a N + 1).toNat
          (configurationTranslation (c N - s) ω)) / (S N).card - ∫ ω', Z ω' ∂μ|}
        ≤ ∫ ω, |(∑ s ∈ S N, LatticeProb.bAvg T Z (b N - a N + 1).toNat
          (configurationTranslation (c N - s) ω)) / (S N).card - ∫ ω', Z ω' ∂μ| ∂μ :=
        mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hint η
      _ ≤ _ := integral_abs_finsetAvg_sub_le (S N) (hS N)
          (fun s => measurePreserving_configurationTranslation p (c N - s))
          (LatticeProb.measurable_bAvg hT.measurable hZm _) (integrable_bAvg hT hZ _) _
  have hreal : Tendsto (fun N => μ.real {ω | η ≤
      |faceAverage Z (F N) (c N) ω - ∫ ω', Z ω' ∂μ|}) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => measureReal_nonneg) hbound ?_
    simpa using ((tendsto_integral_abs_bAvg_sub hT hE hZm hZ).comp hlen).div_const η
  have := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at this
  exact this.congr fun N => ofReal_measureReal (measure_ne_top _ _)

end FaceAverage

end FluxEvent

open FluxEvent in
/-- **`FluxEventStep`** (`step:3.2-event`, eqs. (left-side-large) and (other-sides-small)): with
probability tending to one, the corrected plane `ℓ_{e₁}` has flux at least `(ā/2) N^{d-1}` out of
`L(Q_N)` through `left(Q_N)` and at most `ε N^{d-1}` in absolute value through `sides(Q_N)`.
Hypotheses: the uniqueness of the infinite cluster and the existence of the corrected planes
(Lattice-Probability), Theorem 2.5 (integrability of the side gradients) and the positivity of
the homogenized coefficient (`HomogenizedCoefficientProposed`); the last is proved from the first
three (`homogenizedCoefficientProposed`, `Rigidity/Proofs/S3/HomogenizedCoefficient.lean`). -/
theorem fluxEventStep {d : ℕ} [NeZero d] (hU : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput) (hQ : Rigidity.External.CorrectorQuantitativeInput)
    (hHom : HomogenizedCoefficientProposed) (p : unitInterval) : FluxEventStep d p := by
  intro hd hpc hp1
  unfold HomogenizedCoefficientProposed at hHom
  set μ := latticeBondLaw d p
  obtain ⟨G, hG, hG1, Φ, hΦm, hex, hΦ⟩ := exists_edgeField hU hCorr hd p hpc hp1
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := mem_ae_iff.2 ((prob_compl_eq_zero_iff hG).2 hG1)
  have hall : ∀ᵐ ω ∂μ, ∀ z, configurationTranslation z ω ∈ G :=
    ae_all_iff.2 fun z =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae hGae
  obtain ⟨abar, habar, hX⟩ := hHom d hd p hpc hp1
  obtain ⟨hXi, hXm⟩ := hX (Φ (unit 0) 0) (by
    filter_upwards [hGae] with ω hω h u hu
    exact (hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu _ _).symm)
  have hYi : ∀ j, j ≠ 0 → Integrable (Φ 0 (unit j)) μ := fun j hj =>
    integrable_sideField hQ hd p hpc hp1 hGae hΦm hex hΦ hj
  have hYm : ∀ j, j ≠ 0 → ∫ ω, Φ 0 (unit j) ω ∂μ = 0 := fun j hj =>
    integral_sideField_eq_zero p hGae hex hΦ hj (hYi j hj)
  refine ⟨abar / 2, half_pos habar, fun ε hε => ?_⟩
  set η : ℝ := ε / (2 * d * 3 ^ d) with hηdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hη : 0 < η := by positivity
  let k1 : Fin d := ⟨1, hd⟩
  have hk1 : k1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [k1] at this
  -- the three families of bad events
  set BL : ℕ → Set (Configuration d) := fun N => {ω | abar / 2 ≤
    |faceAverage (Φ (unit 0) 0) (leftFace d N) (unit 0) ω - ∫ ω', Φ (unit 0) 0 ω' ∂μ|}
  set BU : Fin d → ℕ → Set (Configuration d) := fun j N => {ω | η ≤
    |faceAverage (Φ 0 (unit j)) (upperSide j N) 0 ω - ∫ ω', Φ 0 (unit j) ω' ∂μ|}
  set BD : Fin d → ℕ → Set (Configuration d) := fun j N => {ω | η ≤
    |faceAverage (Φ 0 (unit j)) (lowerSide j N) (unit j) ω - ∫ ω', Φ 0 (unit j) ω' ∂μ|}
  have hL : Tendsto (fun N => μ (BL N)) atTop (𝓝 0) :=
    tendsto_measure_faceAverage p (hΦm _ _) hXi k1 (fun N => leftFace d N) (fun _ => unit 0)
      (fun N => -(N : ℤ)) (fun N => (N : ℤ)) (fun N => show -(N : ℤ) ≤ N by omega)
      (tendsto_atTop_mono (fun N => show N ≤ ((N : ℤ) - -(N : ℤ) + 1).toNat by omega)
        tendsto_id)
      (fun N x => mem_leftFace_iff N hk1 x)
      (fun N => ⟨fun _ => -(N : ℤ),
        Finset.mem_filter.2 ⟨mem_latticeCube.2 fun _ => ⟨le_rfl, by omega⟩, rfl⟩⟩) (half_pos habar)
  have hUp : ∀ j ∈ Finset.univ.erase (0 : Fin d), Tendsto (fun N => μ (BU j N)) atTop (𝓝 0) := by
    intro j hj
    have hj0 := Finset.ne_of_mem_erase hj
    exact tendsto_measure_faceAverage p (hΦm _ _) (hYi j hj0) 0 (fun N => upperSide j N)
      (fun _ => 0) (fun N => -(N : ℤ)) (fun _ => 0) (fun N => show -(N : ℤ) ≤ 0 by omega)
      (tendsto_atTop_mono (fun N => show N ≤ ((0 : ℤ) - -(N : ℤ) + 1).toNat by omega)
        tendsto_id)
      (fun N x => mem_side_iff N hj0 (N : ℤ) x)
      (fun N => ⟨fun i => if i = j then (N : ℤ) else -(N : ℤ),
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_latticeCube.2 fun i => by
          split_ifs <;> omega, by simp only [if_neg (Ne.symm hj0)]; omega⟩, if_pos rfl⟩⟩) hη
  have hLow : ∀ j ∈ Finset.univ.erase (0 : Fin d), Tendsto (fun N => μ (BD j N)) atTop (𝓝 0) := by
    intro j hj
    have hj0 := Finset.ne_of_mem_erase hj
    exact tendsto_measure_faceAverage p (hΦm _ _) (hYi j hj0) 0 (fun N => lowerSide j N)
      (fun _ => unit j) (fun N => -(N : ℤ)) (fun _ => 0) (fun N => show -(N : ℤ) ≤ 0 by omega)
      (tendsto_atTop_mono (fun N => show N ≤ ((0 : ℤ) - -(N : ℤ) + 1).toNat by omega)
        tendsto_id)
      (fun N x => mem_side_iff N hj0 (-(N : ℤ)) x)
      (fun N => ⟨fun _ => -(N : ℤ), Finset.mem_filter.2 ⟨Finset.mem_filter.2
        ⟨mem_latticeCube.2 fun _ => ⟨le_rfl, by omega⟩, show -(N : ℤ) ≤ 0 by omega⟩, rfl⟩⟩) hη
  have hnull : μ {ω | ¬ ∀ z, configurationTranslation z ω ∈ G} = 0 := ae_iff.1 hall
  -- outside the bad events, the corrected plane has the required fluxes
  have hsub : ∀ N : ℕ, 1 ≤ N → {ω | ¬ ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
        abar / 2 * (N : ℝ) ^ ((d : ℝ) - 1) ≤ leftFlux (uniqueInfiniteComponent h) u N ∧
        |sideFlux (uniqueInfiniteComponent h) u N| ≤ ε * (N : ℝ) ^ ((d : ℝ) - 1)} ⊆
      {ω | ¬ ∀ z, configurationTranslation z ω ∈ G} ∪
        (BL N ∪ ⋃ j ∈ Finset.univ.erase (0 : Fin d), (BU j N ∪ BD j N)) := by
    intro N hN ω hbad
    by_contra hgood
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      not_le, not_not, BL, BU, BD] at hgood
    obtain ⟨hω, hLω, hSω⟩ := hgood
    apply hbad
    have hω0 : ω ∈ G := by simpa only [configurationTranslation_zero] using hω 0
    obtain ⟨h, hexu⟩ := hex ω hω0
    have hinf := uniqueInfiniteComponent_infinite h
    obtain ⟨u, hu⟩ := hexu _ hinf
    have key : ∀ x y w, edgeDifference (uniqueInfiniteComponent h) u x y =
        Φ (x - w) (y - w) (configurationTranslation (-w) ω) := by
      intro x y w
      have := edgeDifference_add_eq hΦ hω _ hinf u hu (x - w) (y - w) w
      rwa [sub_add_cancel, sub_add_cancel] at this
    have hpow : (N : ℝ) ^ ((d : ℝ) - 1) = (N : ℝ) ^ (d - 1) := by
      rw [← Real.rpow_natCast, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hcube : ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) ≤ 3 ^ (d - 1) * (N : ℝ) ^ (d - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
    refine ⟨h, u, hu, ?_, ?_⟩
    · -- the left face
      have hne : (leftFace d N).Nonempty := ⟨fun _ => -(N : ℤ),
        Finset.mem_filter.2 ⟨mem_latticeCube.2 fun _ => ⟨le_rfl, by omega⟩, rfl⟩⟩
      have hsum : leftFlux (uniqueInfiniteComponent h) u N =
          faceAverage (Φ (unit 0) 0) (leftFace d N) (unit 0) ω * (leftFace d N).card := by
        rw [← sum_eq_faceAverage_mul _ hne]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [key x (x - unit 0) (x - unit 0), sub_sub_cancel, sub_self, neg_sub]
      have hcard : ((leftFace d N).card : ℝ) = ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) := by
        rw [show leftFace d N = (latticeCube d N).filter (fun x => x 0 = -(N : ℤ)) from rfl,
          card_latticeCube_filter_eq N 0 (-(N : ℤ)) le_rfl (by omega)]
        push_cast
        ring
      have hcardN : (N : ℝ) ^ (d - 1) ≤ ((leftFace d N).card : ℝ) := by
        rw [hcard]
        exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
      rw [hXm] at hLω
      have hA : abar / 2 < faceAverage (Φ (unit 0) 0) (leftFace d N) (unit 0) ω := by
        have := (abs_lt.1 hLω).1
        linarith
      rw [hsum, hpow]
      exact mul_le_mul hA.le hcardN (by positivity) ((half_pos habar).le.trans hA.le)
    · -- the sides
      have hside : ∀ j ∈ Finset.univ.erase (0 : Fin d),
          |∑ x ∈ upperSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x + unit j) +
            ∑ x ∈ lowerSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x - unit j)| ≤
          2 * η * (3 ^ (d - 1) * (N : ℝ) ^ (d - 1)) := by
        intro j hj
        have hj0 := Finset.ne_of_mem_erase hj
        obtain ⟨hUj, hDj⟩ := hSω j hj
        rw [hYm j hj0, sub_zero] at hUj hDj
        have hneU : (upperSide j N).Nonempty :=
          ⟨fun i => if i = j then (N : ℤ) else -(N : ℤ),
            Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_latticeCube.2 fun i => by
              split_ifs <;> omega, by simp only [if_neg (Ne.symm hj0)]; omega⟩, if_pos rfl⟩⟩
        have hneD : (lowerSide j N).Nonempty := ⟨fun _ => -(N : ℤ), Finset.mem_filter.2
          ⟨Finset.mem_filter.2 ⟨mem_latticeCube.2 fun _ => ⟨le_rfl, by omega⟩,
            show -(N : ℤ) ≤ 0 by omega⟩, rfl⟩⟩
        have hU : ∑ x ∈ upperSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x + unit j) =
            faceAverage (Φ 0 (unit j)) (upperSide j N) 0 ω * (upperSide j N).card := by
          rw [← sum_eq_faceAverage_mul _ hneU]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [key x (x + unit j) x, sub_self, add_sub_cancel_left, zero_sub]
        have hD : ∑ x ∈ lowerSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x - unit j) =
            -(faceAverage (Φ 0 (unit j)) (lowerSide j N) (unit j) ω * (lowerSide j N).card) := by
          rw [← sum_eq_faceAverage_mul _ hneD, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [edgeDifference_comm, key (x - unit j) x (x - unit j), sub_self, sub_sub_cancel,
            neg_sub]
        have hcU : ((upperSide j N).card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) := by
          have := card_side_le N j (N : ℤ) (by omega) le_rfl
          exact_mod_cast this
        have hcD : ((lowerSide j N).card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) := by
          have := card_side_le N j (-(N : ℤ)) le_rfl (by omega)
          exact_mod_cast this
        rw [hU, hD]
        calc _ ≤ |faceAverage (Φ 0 (unit j)) (upperSide j N) 0 ω * (upperSide j N).card| +
              |-(faceAverage (Φ 0 (unit j)) (lowerSide j N) (unit j) ω *
                (lowerSide j N).card)| := abs_add_le _ _
          _ ≤ η * ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) + η * ((2 * N + 1 : ℕ) : ℝ) ^ (d - 1) := by
              rw [abs_neg, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
              gcongr
          _ ≤ _ := by nlinarith
      unfold sideFlux sidesSum
      calc _ ≤ ∑ j ∈ Finset.univ.erase (0 : Fin d),
            |∑ x ∈ upperSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x + unit j) +
              ∑ x ∈ lowerSide j N, edgeDifference (uniqueInfiniteComponent h) u x (x - unit j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.univ.erase (0 : Fin d), 2 * η * (3 ^ (d - 1) * (N : ℝ) ^ (d - 1)) :=
            Finset.sum_le_sum hside
        _ ≤ ε * (N : ℝ) ^ ((d : ℝ) - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul, hpow, hηdef]
            have hcard : ((Finset.univ.erase (0 : Fin d)).card : ℝ) ≤ d := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                Fintype.card_fin]
              exact_mod_cast Nat.sub_le d 1
            have h3 : (3 : ℝ) ^ d = 3 * 3 ^ (d - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ d)]
            have hNd : 0 ≤ (N : ℝ) ^ (d - 1) := by positivity
            have h3p : 0 < (3 : ℝ) ^ (d - 1) := by positivity
            rw [h3]
            field_simp
            nlinarith [mul_nonneg (mul_nonneg hNd h3p.le) hε.le]
  -- the measure of the bad event
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h := fun N => μ {ω | ¬ ∀ z, configurationTranslation z ω ∈ G} +
      (μ (BL N) + ∑ j ∈ Finset.univ.erase (0 : Fin d), (μ (BU j N) + μ (BD j N))))
    ?_ (Eventually.of_forall fun _ => zero_le) ?_
  · rw [hnull]
    have := (tendsto_const_nhds (x := (0 : ENNReal))).add (hL.add
      (tendsto_finsetSum _ fun j hj => (hUp j hj).add (hLow j hj)))
    simpa using this
  · filter_upwards [eventually_ge_atTop 1] with N hN
    refine (measure_mono (hsub N hN)).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl ((measure_union_le _ _).trans (add_le_add le_rfl
        ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun j _ => measure_union_le _ _))))))

end Rigidity.Proofs.S3
