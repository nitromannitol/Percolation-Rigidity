import Rigidity.Proofs.S3.EdgeGradient
import Rigidity.Proofs.S3.Reflection
import Rigidity.Proofs.S3.ClosedSlopes
import Rigidity.Steps.S3.ReductionToSlopeE1
import Rigidity.Steps.S3.NotLipschitzInner

/-!
# Proposition 3.2 at a general slope `q ≠ 0`

`NotLipschitzAtStmt d p q` is the first assertion of Proposition 3.2 (`prop:not-lipschitz`,
corrected draft L864-1112) with the slope `e₁` replaced by `q`: for every `L ≥ 1`, with positive
probability the origin lies in the infinite cluster and some corrected plane `ℓ_q` has
`|∇ℓ_q(0)| > L`. At `d = 2` its body is that of `NotLipschitzAtStep p q` of
`Rigidity/Steps/Section5/GeneralSlope.lean` (the input of Proposition 5.11 at slope `q`), so
`fun L hL => notLipschitzAt_of_steps … hq L hL` proves `NotLipschitzAtStep p q`.

Route. Rather than repeating the proof of Proposition 3.2 with the cube `Q_N` cut perpendicular to a
coordinate `i` with `qᵢ ≠ 0`, the slope-`q` statement is reduced to the slope-`e₁` statement by the
reflection argument of Lemma 3.1 (`step:3.1-closed-slopes`, `step:3.1-reflection`, corrected draft
L825-859):
* `edgeGradientAtStep` (stationarity, the preamble L952 of the proof of Proposition 3.2 at slope
  `q`): if `|∇ℓ_q(0)| ≤ L` almost surely, then almost surely every corrected plane of slope `q` is
  `L`-Lipschitz on the infinite cluster;
* `ae_slopeE1_mem_lipschitzSlopeSet` (the end of the proof of Lemma 3.1, L841-859): if a fixed
  nonzero slope `q` is almost surely `L`-Lipschitz, then `e₁` is almost surely
  `|q_j|⁻¹ L`-Lipschitz for a coordinate `j` with `q_j ≠ 0`;
* the second assertion of Proposition 3.2 (slope `e₁`) excludes the latter.

So `NotLipschitzAtStmt d p q` needs no slope-`q` form of the positivity of the homogenized
coefficient (`Rigidity.Proofs.S3.HomogenizedCoefficientProposed`, slope `e₁`, proved from
literature inputs in `Rigidity/Proofs/S3/HomogenizedCoefficient.lean`) beyond its use in
Proposition 3.2. (In a direct proof along `Rigidity/Steps/S3/NotLipschitz.lean`, every step but
`FluxEventStep` is slope-free or proved at every slope, and `false_of_steps_at` uses the slope only
as a parameter; `FluxEventStep` would need the mean `ā q₁` of the gradient of `ℓ_q` across a
horizontal edge, `q₁ > 0`.)
`notLipschitzAt_of_steps` takes Proposition 3.2 as a hypothesis; `notLipschitzAt` discharges
`ClosedSlopesStep` and `ReflectionStep` with their proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Section3

namespace Rigidity.Steps.S3

variable {d : ℕ}

/-- Proposition 3.2 at slope `q` (first assertion): for every `L ≥ 1`, with positive probability
the origin lies in the unique infinite cluster and some corrected plane of slope `q` has
`|∇ℓ_q(0)| > L` (positive outer measure). For `q = e₁` it follows from the first conjunct of
`NotLipschitzStmt d p` (inner-measure form, `NotLipschitzStmt.originGradient_ne_zero`); for `d = 2`
it is `NotLipschitzAtStep p q` of `Rigidity/Steps/Section5/GeneralSlope.lean`. -/
def NotLipschitzAtStmt (d : ℕ) [NeZero d] (p : unitInterval) (q : Fin d → ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L →
    latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∃ ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp,
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
          L < originGradientNorm (uniqueInfiniteComponent h) ho u} ≠ 0

/-- `EdgeGradientStep` at slope `q` (preamble L952 of the proof of Proposition 3.2,
stationarity): if `|∇ℓ_q(0)| ≤ L` almost surely, then almost surely every corrected plane of slope
`q` is `L`-Lipschitz on the infinite cluster. -/
def EdgeGradientAtStep (d : ℕ) [NeZero d] (p : unitInterval) (q : Fin d → ℝ) : Prop :=
  ∀ L : ℝ, latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp,
      ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
        L < originGradientNorm (uniqueInfiniteComponent h) ho u} = 0 →
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∀ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u →
        IsLipschitzWith (uniqueInfiniteComponent h) L u

/-- `EdgeGradientAtStep` holds at every slope: a gradient larger than `L` along an open edge
`(x, x + eᵢ)` of the cluster becomes, after translating the environment by `-x`, a gradient larger
than `L` at the origin (`EdgeGradient.edgeEvent_subset_preimage`, slope-free), and the countable
union over the edges of these null events is null. The proof of `Proofs.S3.edgeGradientStep` with
`e₁` replaced by `q`. -/
theorem edgeGradientAtStep [NeZero d] (p : unitInterval) (q : Fin d → ℝ) :
    EdgeGradientAtStep d p q := by
  intro L h0
  have hF : ∀ x i, latticeBondLaw d p (Proofs.S3.EdgeGradient.edgeEvent q L x i) = 0 :=
    fun x i => measure_mono_null (Proofs.S3.EdgeGradient.edgeEvent_subset_preimage q L x i)
      (((measurePreserving_configurationTranslation p (-x)).measure_preimage
        (NullMeasurableSet.of_null h0)).trans h0)
  have hae : ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ x i, ω ∉ Proofs.S3.EdgeGradient.edgeEvent q L x i := by
    rw [ae_all_iff]
    intro x
    rw [ae_all_iff]
    intro i
    exact measure_eq_zero_iff_ae_notMem.1 (hF x i)
  filter_upwards [hae] with ω hω h u hu
  rw [IsLipschitzWith, component_dist_bound_iff_edge_bound]
  intro a b hab
  have hadj : (openGraph ω).Adj a.val b.val :=
    ((uniqueInfiniteComponent h).toSimpleGraph_adj a.2 b.2).1 hab
  obtain ⟨i, hi | hi⟩ := hadj.1
  · by_contra hlt
    refine hω a.val i ⟨h, u, hu, a, b, rfl, hi, ?_, lt_of_not_ge hlt⟩
    rw [← hi]
    exact hadj
  · by_contra hlt
    refine hω b.val i ⟨h, u, hu, b, a, rfl, hi, ?_, ?_⟩
    · rw [← hi]
      exact hadj.symm
    · rw [abs_sub_comm]
      exact lt_of_not_ge hlt

/-- The reflection argument at the end of the proof of Lemma 3.1 (`step:3.1-reflection`,
`step:3.1-closed-slopes`, corrected draft L841-859): if a fixed nonzero slope `q` is almost surely
`L`-Lipschitz, then after a coordinate transposition making the first coordinate `r₁ = q_j`
nonzero, averaging with the reflections `T_j` zeroes the other coordinates, and `e₁ = r₁⁻¹ r₁ e₁`
is almost surely `|r₁|⁻¹ L`-Lipschitz. -/
theorem ae_slopeE1_mem_lipschitzSlopeSet [NeZero d] {p : unitInterval}
    (hclosed : ClosedSlopesStep d p) (hrefl : ReflectionStep d p) {L : ℝ} (hL : 0 < L)
    {q : Fin d → ℝ} (hq0 : q ≠ 0) (hq : ∀ᵐ ω ∂latticeBondLaw d p, q ∈ lipschitzSlopeSet ω L) :
    ∃ L' : ℝ, 0 < L' ∧ ∀ᵐ ω ∂latticeBondLaw d p, slopeE1 d ∈ lipschitzSlopeSet ω L' := by
  obtain ⟨j, hj⟩ : ∃ j, q j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hq0 (funext hcon)
  set r : Fin d → ℝ := q ∘ Equiv.swap 0 j with hr_def
  have hr : ∀ᵐ ω ∂latticeBondLaw d p, r ∈ lipschitzSlopeSet ω L := (hrefl L q hq).2 0 j
  have hr0 : r 0 ≠ 0 := by
    simpa [hr_def, Equiv.swap_apply_left] using hj
  have hzero : ∀ s : Finset (Fin d),
      ∀ᵐ ω ∂latticeBondLaw d p, zeroSlope s r ∈ lipschitzSlopeSet ω L := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show zeroSlope ∅ r = r from funext fun i => by simp [zeroSlope]]
      exact hr
    | insert i s _ ih =>
      filter_upwards [ih, (hrefl L _ ih).1 i, hclosed] with ω h1 h2 hω
      have hmem := (hω L).2 L (1 / 2) (1 / 2) _ _ h1 h2
      rwa [half_add_half_reflectSlope_zeroSlope,
        show |(1 / 2 : ℝ)| * L + |(1 / 2 : ℝ)| * L = L by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring] at hmem
  refine ⟨|r 0|⁻¹ * L, by positivity, ?_⟩
  filter_upwards [hzero (Finset.univ.erase 0), hclosed] with ω h1 hω
  have hmem := (hω L).2 L (r 0)⁻¹ 0 _ _ h1 h1
  rw [zeroSlope_erase_zero, smul_smul, inv_mul_cancel₀ hr0, one_smul, zero_smul, add_zero,
    abs_inv, abs_zero, zero_mul, add_zero] at hmem
  exact hmem

/-- **Proposition 3.2 at slope `q`** from Proposition 3.2 (slope `e₁`), the almost sure
uniqueness of the infinite cluster, and the steps `step:3.1-closed-slopes` and
`step:3.1-reflection` of Lemma 3.1. If `|∇ℓ_q(0)| ≤ L` almost surely, then `ℓ_q` is almost surely
`L`-Lipschitz (`edgeGradientAtStep`), hence `ℓ_{e₁}` is almost surely `L'`-Lipschitz
(`ae_slopeE1_mem_lipschitzSlopeSet`), against the second assertion of Proposition 3.2 at
`max 1 L'`. -/
theorem notLipschitzAt_of_steps [NeZero d] {p : unitInterval} (h32 : NotLipschitzStmt d p)
    (hU : latticeBondLaw d p (uniqueInfiniteComponentEvent d) = 1)
    (hclosed : ClosedSlopesStep d p) (hrefl : ReflectionStep d p) {q : Fin d → ℝ}
    (hq : q ≠ 0) : NotLipschitzAtStmt d p q := by
  intro L hL h0
  have hUae : ∀ᵐ ω ∂latticeBondLaw d p, HasUniqueInfiniteOpenComponent ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent d)).2 hU
  have hqae : ∀ᵐ ω ∂latticeBondLaw d p, q ∈ lipschitzSlopeSet ω L := by
    filter_upwards [edgeGradientAtStep p q L h0, hUae] with ω hω hu
    exact ⟨hu, hω hu⟩
  obtain ⟨L', -, hL'⟩ :=
    ae_slopeE1_mem_lipschitzSlopeSet hclosed hrefl (by linarith) hq hqae
  refine (h32.notLipschitzWith_ne_zero (le_max_left 1 L')) (measure_mono_null ?_ (ae_iff.1 hL'))
  rintro ω ⟨h, u, hu, hnl⟩ ⟨h₁, hall⟩
  exact hnl (isLipschitzWith_mono (hall u hu) (le_max_right 1 L'))

/-- **Proposition 3.2 at every slope `q ≠ 0`** for `d ≥ 2` and `p_c(d) < p < 1`, from
Proposition 3.2 (slope `e₁`) and the cited inputs of `step:3.1-closed-slopes` (uniqueness of the
infinite cluster and the corrector). -/
theorem notLipschitzAt [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (h32 : NotLipschitzStmt d p) {q : Fin d → ℝ} (hq : q ≠ 0) : NotLipschitzAtStmt d p q :=
  notLipschitzAt_of_steps h32 (hclassical.2 d hd p hpc hp1)
    (Proofs.S3.closedSlopesStep hclassical hcorrector hd p hpc hp1) (Proofs.S3.reflectionStep p) hq

end Rigidity.Steps.S3
