import Rigidity.Steps.S3.NotLipschitz
import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw

/-!
# Proposition 3.2: stationarity of the gradient of the corrected plane

Step `EdgeGradientStep` of Proposition 3.2 (preamble of the proof, corrected draft L952). If a
corrected plane of slope `q` on the infinite cluster has a gradient larger than `L` along the
open edge `(x, x + eᵢ)`, then translating the environment by `-x` moves this edge to the edge
`(0, eᵢ)` at the origin: the infinite cluster moves with the environment
(`openComponentTranslation_uniqueInfiniteComponent`), and so do the corrected planes
(`isCorrectedPlane_translation_iff`), so `|∇ℓ(0)| > L` for the translated corrected plane. The
law of the environment is translation invariant (`measurePreserving_configurationTranslation`),
so if `|∇ℓ_{e₁}(0)| > L` has probability zero, then almost surely no corrected plane of slope `e₁`
has a gradient larger than `L` along any open edge of the infinite cluster (a countable union of
null events). A bound on the gradients along the open edges is the `L`-Lipschitz bound for the
graph distance (`component_dist_bound_iff_edge_bound`).
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

namespace EdgeGradient

/-- The event that some corrected plane of slope `q` on the infinite cluster has a gradient
larger than `L` along the open edge `(x, x + eᵢ)`. -/
def edgeEvent (q : Fin d → ℝ) (L : ℝ) (x : Vertex d) (i : Fin d) : Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ u : uniqueInfiniteComponent h → ℝ,
    IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
    ∃ a b : uniqueInfiniteComponent h, a.val = x ∧ b.val = x + unit i ∧
      (openGraph ω).Adj x (x + unit i) ∧ L < |u a - u b|}

/-- The event that some corrected plane of slope `q` on the infinite cluster has `|∇u(0)| > L`
(the event of the hypothesis of `EdgeGradientStep`). -/
def originEvent (q : Fin d → ℝ) (L : ℝ) : Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∃ ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp,
    ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
      L < originGradientNorm (uniqueInfiniteComponent h) ho u}

/-- Translation covariance: a gradient larger than `L` along the open edge `(x, x + eᵢ)` becomes,
after translating the environment by `-x`, a gradient larger than `L` along the edge `(0, eᵢ)`,
hence `|∇u(0)| > L` for the translated corrected plane. -/
theorem edgeEvent_subset_preimage (q : Fin d → ℝ) (L : ℝ) (x : Vertex d) (i : Fin d) :
    edgeEvent q L x i ⊆ configurationTranslation (-x) ⁻¹' originEvent q L := by
  rintro ω ⟨h, u, hu, a, b, rfl, hb, hadj, hL⟩
  refine ⟨(hasUniqueInfiniteOpenComponent_translation_iff (-a.val) ω).mpr h, ?_⟩
  rw [← openComponentTranslation_uniqueInfiniteComponent (-a.val) h]
  have ho : (0 : Vertex d) ∈
      (openComponentTranslation (-a.val) ω (uniqueInfiniteComponent h)).supp := by
    rw [mem_openComponentTranslation_supp, zero_sub, neg_neg]
    exact a.2
  refine ⟨ho, fun y => u ((openComponentTranslationIso (-a.val) _).symm y),
    (isCorrectedPlane_translation_iff (-a.val) _ q u).2 hu, hL.trans_le ?_⟩
  have hadj' : (openGraph (configurationTranslation (-a.val) ω)).Adj 0 (unit i) := by
    have h' := (openGraph_adj_translation_iff (-a.val) ω a.val (a.val + unit i)).2 hadj
    have e₁ : a.val + -a.val = 0 := add_neg_cancel _
    have e₂ : a.val + unit i + -a.val = unit i := by abel
    rwa [e₁, e₂] at h'
  unfold originGradientNorm
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => ?_) (Finset.mem_univ i))
  · dsimp only
    rw [dif_pos hadj']
    have ea : a = (openComponentTranslationIso (-a.val) (uniqueInfiniteComponent h)).symm
        ⟨0, ho⟩ := Subtype.ext (by rw [openComponentTranslationIso_symm_val]; simp)
    have eb : b = (openComponentTranslationIso (-a.val) (uniqueInfiniteComponent h)).symm
        ⟨unit i, (openComponentTranslation (-a.val) ω _).mem_supp_of_adj_mem_supp ho hadj'⟩ :=
      Subtype.ext (by rw [openComponentTranslationIso_symm_val, hb]; abel)
    rw [← ea, ← eb]
  · dsimp only
    split_ifs
    exacts [abs_nonneg _, le_rfl]

end EdgeGradient

open EdgeGradient in
/-- `EdgeGradientStep` (preamble of the proof of Proposition 3.2, L952): if `|∇ℓ_{e₁}(0)| ≤ L`
almost surely, then by stationarity almost surely every corrected plane of slope `e₁` on the
infinite cluster is `L`-Lipschitz. -/
theorem edgeGradientStep [NeZero d] (p : unitInterval) : EdgeGradientStep d p := by
  intro L h0
  have hF : ∀ x i, latticeBondLaw d p (edgeEvent (slopeE1 d) L x i) = 0 := fun x i =>
    measure_mono_null (edgeEvent_subset_preimage (slopeE1 d) L x i)
      (((measurePreserving_configurationTranslation p (-x)).measure_preimage
        (NullMeasurableSet.of_null h0)).trans h0)
  have hae : ∀ᵐ ω ∂latticeBondLaw d p, ∀ x i, ω ∉ edgeEvent (slopeE1 d) L x i := by
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

end Rigidity.Proofs.S3
