import Rigidity.External.PlanarInputs
import Rigidity.Proofs.Partition.Uniqueness
import LatticeProb.Prob.Percolation.MeasurableRootedPlane
import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra

/-!
# A measurable planar corrector

The corrector `χ_q` of Dario's §2 is defined up to an additive constant; only its increments
`χ_q(a) - χ_q(b)` on the infinite cluster are used. On a measurable conull set `G` where the infinite
cluster is unique and the planar qualitative corrector input holds
(`exists_measurable_correctorValid_two`), the corrected plane of slope `q` vanishing at `b` has a
measurable encoding (`LatticeProb.Percolation.exists_measurable_rooted_plane_on_valid_set`), and
`correctorDiff q ω a b` is its value at `a` minus `q · (a - b)`. It is measurable in `ω`
(`measurable_correctorDiff`), equal to `(ℓ(a) - q · a) - (ℓ(b) - q · b)` for every corrected plane
`ℓ` of slope `q` on the infinite cluster (`correctorDiff_eq`), additive along chains
(`correctorDiff_add`) and invariant under translations of the configuration
(`correctorDiff_translation`), which is the stationarity (2.3) of Dario.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped Classical

/-- A measurable conull set of configurations on which the infinite cluster is unique and the
planar qualitative corrector input holds. -/
theorem exists_measurable_correctorValid_two (hC : SupercriticalBondCorrectorInputTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ G : Set (Configuration 2), MeasurableSet G ∧ (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) ∧
      G ⊆ correctorValidEvent 2 := by
  have hae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ correctorValidEvent 2 :=
    (Rigidity.Percolation.ae_hasUniqueInfiniteOpenComponent le_rfl hpc).and (hC p hpc hp1)
  have heq : (Set.univ : Set (Configuration 2)) =ᵐ[latticeBondLaw 2 p]
      correctorValidEvent 2 := by
    filter_upwards [hae] with ω hω
    exact propext ⟨fun _ => hω, fun _ => Set.mem_univ ω⟩
  have hnull : NullMeasurableSet (correctorValidEvent 2) (latticeBondLaw 2 p) :=
    MeasurableSet.univ.nullMeasurableSet.congr heq
  obtain ⟨G, hsub, hG, heqG⟩ := hnull.exists_measurable_subset_ae_eq
  refine ⟨G, hG, ?_, hsub⟩
  filter_upwards [hae, heqG] with ω hω heqω
  exact heqω.mpr hω

/-- Every infinite component of a valid configuration carries a corrected plane of each slope. -/
theorem exists_correctedPlane_of_valid {ω : Configuration 2} (hv : ω ∈ correctorValidEvent 2)
    {K : OpenComponent ω} (hKinf : K.supp.Infinite) (q : Fin 2 → ℝ) :
    ∃ ℓ : K → ℝ, IsCorrectedPlane K q ℓ := by
  obtain ⟨h, hv⟩ := hv
  have hK : K = uniqueInfiniteComponent h := (eq_uniqueInfiniteComponent_iff h K).2 hKinf
  subst hK
  obtain ⟨o, ho⟩ := hKinf.nonempty
  obtain ⟨ℓ, hℓ, -⟩ := (hv h).1 q ⟨o, ho⟩
  exact ⟨ℓ, hℓ.1⟩

section Carrier

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The measurable encoding of the corrected plane of slope `q` vanishing at the root `o`. -/
noncomputable def rootedPlaneField (o : Vertex 2) :
    (↥(G ∩ infiniteComponentEvent o) × (Fin 2 → ℝ)) → (Vertex 2 → ℝ) :=
  Classical.choose (exists_measurable_rooted_plane_on_valid_set G hG hGv o)

theorem measurable_rootedPlaneField (o : Vertex 2) : Measurable (rootedPlaneField hG hGv o) :=
  (Classical.choose_spec (exists_measurable_rooted_plane_on_valid_set G hG hGv o)).1

theorem rootedPlaneField_spec (o : Vertex 2) (z : ↥(G ∩ infiniteComponentEvent o) × (Fin 2 → ℝ)) :
    rootedPlaneField hG hGv o z o = 0 ∧
      IsCorrectedPlane ((openGraph z.1.val).connectedComponentMk o) z.2
        (fun x => rootedPlaneField hG hGv o z x.val) :=
  have h := ((Classical.choose_spec
    (exists_measurable_rooted_plane_on_valid_set G hG hGv o)).2 z _).2 rfl
  ⟨h.1, h.2.1⟩

/-- The corrector increment `χ_q(a) - χ_q(b)`: the value at `a` of the corrected plane of slope
`q` vanishing at `b`, minus `q · (a - b)`; `0` when `ω ∉ G` or the component of `b` is finite. -/
noncomputable def correctorDiff (q : Fin 2 → ℝ) (ω : Configuration 2) (a b : Vertex 2) : ℝ :=
  if h : ω ∈ G ∩ infiniteComponentEvent b then
    rootedPlaneField hG hGv b (⟨ω, h⟩, q) a - ∑ i, q i * (a i : ℝ) + ∑ i, q i * (b i : ℝ)
  else 0

theorem measurable_correctorDiff (q : Fin 2 → ℝ) (a b : Vertex 2) :
    Measurable fun ω => correctorDiff hG hGv q ω a b := by
  unfold correctorDiff
  refine Measurable.dite (f := fun z : ↥(G ∩ infiniteComponentEvent b) =>
      rootedPlaneField hG hGv b (z, q) a - ∑ i, q i * (a i : ℝ) + ∑ i, q i * (b i : ℝ))
    (g := fun _ => (0 : ℝ)) ?_ measurable_const (hG.inter (measurableSet_infiniteComponentEvent b))
  exact (((measurable_pi_apply a).comp ((measurable_rootedPlaneField hG hGv b).comp
    (measurable_id.prodMk measurable_const))).sub_const _).add_const _

/-- The rooted value of a corrected plane on the component of the root. -/
theorem rootedPlaneField_eq {ω : Configuration 2} {b : Vertex 2}
    (hmem : ω ∈ G ∩ infiniteComponentEvent b) (q : Fin 2 → ℝ) {K : OpenComponent ω}
    (hK : (openGraph ω).connectedComponentMk b = K) {ℓ : K → ℝ} (hℓ : IsCorrectedPlane K q ℓ)
    (a : K) (hbK : b ∈ K.supp) :
    rootedPlaneField hG hGv b (⟨ω, hmem⟩, q) a.val = ℓ a - ℓ ⟨b, hbK⟩ := by
  subst hK
  obtain ⟨hU0, hUc⟩ := rootedPlaneField_spec hG hGv b (⟨ω, hmem⟩, q)
  have hℓ' : IsCorrectedPlane ((openGraph ω).connectedComponentMk b) q
      (ℓ - fun _ => ℓ ⟨b, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩) := by
    simpa only [sub_zero] using isCorrectedPlane_sub _ hℓ (isCorrectedPlane_const _
      (ℓ ⟨b, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩))
  have huniq := existsUnique_rooted_plane_of_valid (hGv hmem.1) b hmem.2 q
  have heq := huniq.unique ⟨hUc, hU0⟩ ⟨hℓ', by simp⟩
  exact congrFun heq a

/-- **The corrector increment as a corrected-plane increment.** -/
theorem correctorDiff_eq {q : Fin 2 → ℝ} {ω : Configuration 2} (hω : ω ∈ G)
    {K : OpenComponent ω} (hKinf : K.supp.Infinite) {ℓ : K → ℝ} (hℓ : IsCorrectedPlane K q ℓ)
    (a b : K) :
    correctorDiff hG hGv q ω a.val b.val =
      (ℓ a - ∑ i, q i * (a.val i : ℝ)) - (ℓ b - ∑ i, q i * (b.val i : ℝ)) := by
  have hK : (openGraph ω).connectedComponentMk b.val = K :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff K b.val).1 b.2
  have hb : ω ∈ infiniteComponentEvent b.val := by
    change ((openGraph ω).connectedComponentMk b.val).supp.Infinite
    rw [hK]
    exact hKinf
  have hmem : ω ∈ G ∩ infiniteComponentEvent b.val := ⟨hω, hb⟩
  unfold correctorDiff
  rw [dif_pos hmem, rootedPlaneField_eq hG hGv hmem q hK hℓ a b.2, Subtype.coe_eta]
  ring

/-- Increments add along chains in an infinite component. -/
theorem correctorDiff_add {q : Fin 2 → ℝ} {ω : Configuration 2} (hω : ω ∈ G)
    {K : OpenComponent ω} (hKinf : K.supp.Infinite) (a b c : K) :
    correctorDiff hG hGv q ω a.val c.val =
      correctorDiff hG hGv q ω a.val b.val + correctorDiff hG hGv q ω b.val c.val := by
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω) hKinf q
  rw [correctorDiff_eq hG hGv hω hKinf hℓ, correctorDiff_eq hG hGv hω hKinf hℓ,
    correctorDiff_eq hG hGv hω hKinf hℓ]
  ring

theorem correctorDiff_self {q : Fin 2 → ℝ} {ω : Configuration 2} (hω : ω ∈ G)
    {K : OpenComponent ω} (hKinf : K.supp.Infinite) (a : K) :
    correctorDiff hG hGv q ω a.val a.val = 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω) hKinf q
  rw [correctorDiff_eq hG hGv hω hKinf hℓ]
  ring

theorem correctorDiff_swap {q : Fin 2 → ℝ} {ω : Configuration 2} (hω : ω ∈ G)
    {K : OpenComponent ω} (hKinf : K.supp.Infinite) (a b : K) :
    correctorDiff hG hGv q ω b.val a.val = -correctorDiff hG hGv q ω a.val b.val := by
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω) hKinf q
  rw [correctorDiff_eq hG hGv hω hKinf hℓ, correctorDiff_eq hG hGv hω hKinf hℓ]
  ring

/-- **Stationarity of the corrector increments** (Dario, (2.3)): translating the configuration
by `z` translates the increments. -/
theorem correctorDiff_translation {q : Fin 2 → ℝ} {ω : Configuration 2} (z : Vertex 2)
    (hω : ω ∈ G) (hω' : configurationTranslation z ω ∈ G) {K : OpenComponent ω}
    (hKinf : K.supp.Infinite) (a b : K) :
    correctorDiff hG hGv q (configurationTranslation z ω) (a.val + z) (b.val + z) =
      correctorDiff hG hGv q ω a.val b.val := by
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω) hKinf q
  set K' := openComponentTranslation z ω K
  have hK'inf : K'.supp.Infinite := (openComponentTranslation_infinite_iff z K).2 hKinf
  have hℓ' : IsCorrectedPlane K' q (fun y => ℓ ((openComponentTranslationIso z K).symm y)) :=
    (isCorrectedPlane_translation_iff z K q ℓ).2 hℓ
  have h1 := correctorDiff_eq hG hGv hω' hK'inf hℓ' (openComponentTranslationIso z K a)
    (openComponentTranslationIso z K b)
  simp only [RelIso.symm_apply_apply, openComponentTranslationIso_val] at h1
  rw [h1, correctorDiff_eq hG hGv hω hKinf hℓ]
  simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
  ring

end Carrier

end Rigidity.Corrector
