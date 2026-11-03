import Rigidity.Draft.Section3Statements
import LatticeProb.Prob.Percolation.MeasurableRootedPlane
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra

/-!
# Proposition 3.2 in inner-measure form

The draft `NotLipschitzStmt` states "with positive probability" in the inner-measure form: each
event contains a measurable event of positive probability. The proof of Proposition 3.2 is by
contradiction and gives positivity of the outer measure of the event
`originGradientEvent d L = {0 ∈ 𝒞_∞, |∇ℓ_{e₁}(0)| > L}`. This file turns it into the inner-measure
form with the measurable rooted plane field of Lattice-Probability: on a measurable conull set of
environments where the corrected planes exist and are unique up to additive constants
(`SupercriticalBondCorrectorInput`), `|∇ℓ_{e₁}(0)|` is a measurable function of the environment, and
the event agrees with a measurable event off a null set.

* `notLipschitzStmt_of_originGradient`: the draft statement from the outer-measure bound.
* `NotLipschitzStmt.originGradient_ne_zero`, `NotLipschitzStmt.notLipschitzWith_ne_zero`: the
  outer-measure consequences used by the consumers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation LatticeProb.External Rigidity.Section3
open Classical

namespace Rigidity.Steps.S3

variable {d : ℕ}

/-- The event of the first assertion of Proposition 3.2: the origin lies in the infinite cluster
and some corrected plane `ℓ_{e₁}` has `|∇ℓ_{e₁}(0)| > L`. -/
def originGradientEvent (d : ℕ) [NeZero d] (L : ℝ) : Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∃ ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp,
    ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
      L < originGradientNorm (uniqueInfiniteComponent h) ho u}

/-- The event of the second assertion of Proposition 3.2: some corrected plane `ℓ_{e₁}` is not
`L`-Lipschitz. -/
def notLipschitzWithEvent (d : ℕ) [NeZero d] (L : ℝ) : Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u ∧
      ¬ IsLipschitzWith (uniqueInfiniteComponent h) L u}

/-- `|∇u(0)| > d L` forces a gradient larger than `L` along an edge at the origin. -/
theorem not_isLipschitzWith_of_lt_originGradientNorm {ω : Configuration d} {C : OpenComponent ω}
    (ho : (0 : Vertex d) ∈ C.supp) {u : C → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlt : (d : ℝ) * L < originGradientNorm C ho u) : ¬ IsLipschitzWith C L u := by
  intro hLip
  refine absurd hlt (not_lt.2 ?_)
  unfold originGradientNorm
  calc _ ≤ ∑ _i : Fin d, L := Finset.sum_le_sum fun i _ => ?_
    _ = d * L := by simp
  split_ifs with hi
  · have hy := C.mem_supp_of_adj_mem_supp ho hi
    have hadj : (componentGraph C).Adj ⟨0, ho⟩ ⟨unit i, hy⟩ := (C.toSimpleGraph_adj ho hy).2 hi
    have := hLip ⟨0, ho⟩ ⟨unit i, hy⟩
    rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at this
    simpa using this
  · exact hL

section Consequences

variable [NeZero d] {p : unitInterval}

/-- The first assertion of Proposition 3.2 gives positive outer measure. -/
theorem _root_.Rigidity.Section3.NotLipschitzStmt.originGradient_ne_zero
    (h : NotLipschitzStmt d p) {L : ℝ} (hL : 1 ≤ L) :
    latticeBondLaw d p (originGradientEvent d L) ≠ 0 := by
  obtain ⟨A, hA, -, hpos⟩ := (h L hL).1
  exact (hpos.trans_le (measure_mono hA)).ne'

/-- The second assertion of Proposition 3.2 gives positive outer measure. -/
theorem _root_.Rigidity.Section3.NotLipschitzStmt.notLipschitzWith_ne_zero
    (h : NotLipschitzStmt d p) {L : ℝ} (hL : 1 ≤ L) :
    latticeBondLaw d p (notLipschitzWithEvent d L) ≠ 0 := by
  obtain ⟨A, hA, -, hpos⟩ := (h L hL).2
  exact (hpos.trans_le (measure_mono hA)).ne'

end Consequences

/-! ### The measurable rooted plane field at the origin -/

/-- A corrected plane minus a constant, extended by zero off its component, is a corrected plane
of any equal component. -/
theorem isCorrectedPlane_extend_sub_const {ω : Configuration d} {C D : OpenComponent ω}
    (hDC : D = C) {q : Fin d → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) (c : ℝ) :
    IsCorrectedPlane D q
      (fun x => if hx : x.val ∈ C.supp then ℓ ⟨x.val, hx⟩ - c else 0) := by
  subst hDC
  have heq : (fun x : D => if hx : x.val ∈ D.supp then ℓ ⟨x.val, hx⟩ - c else 0) =
      ℓ - fun _ => c := by
    funext x
    rw [dif_pos (show x.val ∈ D.supp from x.2)]
    rfl
  rw [heq]
  simpa only [sub_zero] using isCorrectedPlane_sub D hℓ (isCorrectedPlane_const D c)

/-- The measurable rooted plane field at the root `0` is a corrected plane of the unique infinite
cluster minus its value at the origin (any dimension). -/
theorem rootedPlane_eq_sub {G : Set (Configuration d)}
    {F : (↥(G ∩ infiniteComponentEvent 0) × (Fin d → ℝ)) → (Vertex d → ℝ)}
    (hF : ∀ z U, (U 0 = 0 ∧
        IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk 0) z.2
          (fun x => U x.val) ∧
        ∀ x, ¬ (openGraph z.1.val).Reachable 0 x → U x = 0) ↔ F z = U)
    (z : ↥(G ∩ infiniteComponentEvent 0)) (h : HasUniqueInfiniteOpenComponent z.val)
    (ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp) {q : Fin d → ℝ}
    {ℓ : uniqueInfiniteComponent h → ℝ} (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ)
    {x : Vertex d} (hx : x ∈ (uniqueInfiniteComponent h).supp) :
    F (z, q) x = ℓ ⟨x, hx⟩ - ℓ ⟨0, ho⟩ := by
  have hC0 : (openGraph z.val).connectedComponentMk 0 = uniqueInfiniteComponent h :=
    (eq_uniqueInfiniteComponent_iff h _).mpr z.2.2
  have hval := (hF (z, q) fun y =>
    if hy : y ∈ (uniqueInfiniteComponent h).supp then ℓ ⟨y, hy⟩ - ℓ ⟨0, ho⟩ else 0).mp
    ⟨by simp only [dif_pos ho, sub_self],
      isCorrectedPlane_extend_sub_const hC0 hℓ _,
      fun y hy => by
        refine dif_neg fun hy' => hy ?_
        exact SimpleGraph.ConnectedComponent.exact
          (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 ho).trans
            ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy').symm)⟩
  rw [hval]
  exact dif_pos hx

/-! ### From the outer-measure bound to the inner-measure form -/

variable [NeZero d]

/-- **The event of Proposition 3.2 contains a measurable event of positive probability** as soon as
its outer measure is positive, for `p_c(d) < p < 1`: off the null set where the corrected planes
fail to exist or to be unique up to constants, `|∇ℓ_{e₁}(0)|` is computed from the measurable
rooted plane field. -/
theorem exists_measurable_subset_originGradientEvent (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {L : ℝ}
    (h : latticeBondLaw d p (originGradientEvent d L) ≠ 0) :
    ∃ A ⊆ originGradientEvent d L, MeasurableSet A ∧ 0 < latticeBondLaw d p A := by
  obtain ⟨G, hGm, hG1, hvalid⟩ :=
    exists_measurable_corrector_valid_set hclassical hcorrector d hd p hpc hp1
  obtain ⟨F, hFm, hF⟩ := exists_measurable_rooted_plane_on_valid_set G hGm hvalid 0
  have hB : MeasurableSet (G ∩ infiniteComponentEvent 0) :=
    hGm.inter (measurableSet_infiniteComponentEvent 0)
  have hΦ : ∀ a, Measurable fun z : ↥(G ∩ infiniteComponentEvent 0) => F (z, slopeE1 d) a :=
    fun a => (measurable_pi_apply a).comp (hFm.comp (measurable_id.prodMk measurable_const))
  set g : ↥(G ∩ infiniteComponentEvent 0) → ℝ := fun z => ∑ i : Fin d,
    if (openGraph z.val).Adj 0 (unit i) then
      |F (z, slopeE1 d) 0 - F (z, slopeE1 d) (unit i)| else 0 with hg_def
  have hg : Measurable g := Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurable_subtype_coe (measurableSet_openGraph_adj 0 (unit i)))
      ((hΦ 0).sub (hΦ (unit i))).abs measurable_const
  have key : ∀ (z : ↥(G ∩ infiniteComponentEvent 0)) (h : HasUniqueInfiniteOpenComponent z.val)
      (ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp) (u : uniqueInfiniteComponent h → ℝ),
      IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 d) u →
      g z = originGradientNorm (uniqueInfiniteComponent h) ho u := by
    intro z h ho u hu
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (openGraph z.val).Adj 0 (unit i)
    · rw [if_pos hi, dif_pos hi, rootedPlane_eq_sub hF z h ho hu ho,
        rootedPlane_eq_sub hF z h ho hu
          ((uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hi)]
      congr 1
      ring
    · rw [if_neg hi, dif_neg hi]
  have hGc : latticeBondLaw d p Gᶜ = 0 := (prob_compl_eq_zero_iff hGm).2 hG1
  refine ⟨Subtype.val '' {z | L < g z}, ?_, hB.subtype_image (measurableSet_lt measurable_const hg),
    ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have h := (hvalid z.2.1).1
    have ho : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp :=
      (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
    obtain ⟨u, ⟨hu, -⟩, -⟩ := ((hvalid z.2.1).2 h).1 (slopeE1 d) ⟨0, ho⟩
    exact ⟨h, ho, u, hu, (key z h ho u hu) ▸ hz⟩
  · refine pos_iff_ne_zero.mpr fun hA => h (measure_mono_null ?_ (measure_union_null hA hGc))
    rintro ω ⟨h, ho, u, hu, hlt⟩
    by_cases hωG : ω ∈ G
    · refine Or.inl ⟨⟨ω, hωG, (mem_uniqueInfiniteComponent_iff h 0).mp ho⟩, ?_, rfl⟩
      show L < g _
      rw [key _ h ho u hu]
      exact hlt
    · exact Or.inr hωG

/-- **Proposition 3.2 in the inner-measure form of the draft** from the positivity of the outer
measure of `originGradientEvent d L` for every `L ≥ 1`, the existence and uniqueness of the infinite
cluster and the first-order correctors (`SupercriticalBondCorrectorInput`). The second assertion
is the first one at `d L`. -/
theorem notLipschitzStmt_of_originGradient (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h : ∀ L : ℝ, 1 ≤ L → latticeBondLaw d p (originGradientEvent d L) ≠ 0) :
    NotLipschitzStmt d p := by
  intro L hL
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  obtain ⟨A, hA, hAm, hApos⟩ :=
    exists_measurable_subset_originGradientEvent hclassical hcorrector hd hpc hp1 (h L hL)
  obtain ⟨A', hA', hA'm, hA'pos⟩ := exists_measurable_subset_originGradientEvent hclassical
    hcorrector hd hpc hp1 (h (d * L) (one_le_mul_of_one_le_of_one_le hd1 hL))
  refine ⟨⟨A, hA, hAm, hApos⟩, ⟨A', fun ω hω => ?_, hA'm, hA'pos⟩⟩
  obtain ⟨h, ho, u, hu, hlt⟩ := hA' hω
  exact ⟨h, u, hu, not_isLipschitzWith_of_lt_originGradientNorm ho (by linarith) hlt⟩

end Rigidity.Steps.S3
