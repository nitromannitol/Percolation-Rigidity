import Rigidity.Proofs.Cluster.PlanarOmegaSupRate
import Rigidity.Proofs.Percolation.PlanarLocalStationary

/-!
# Local and stationary versions of `ρ(U)` in dimension two

The proof of Lemma 5.11 of Armstrong and Dario uses local versions `ρ_loc(U)` of
`ρ(U) = sup_q |q|⁻² ω(U, q)₊`, measurable with respect to the bonds near `U`, equal to `ρ(U)` off
an event of small probability, stationary, and independent for well separated cubes ((4.39) and
(4.40) of the source, and the localization and independence displays of the proof of Lemma 5.11,
the latter for distinct subcubes). In dimension two the local
data of the planar partition at `V` (`planarLocalData`) determine `ν(V, ·)` and `μ(V, ·)` on the
good event `PlanarLocalGood` (`planarNu_indicator_eq_of_planarLocalData_eq`,
`planarMu_indicator_eq_of_planarLocalData_eq`), for all slopes at once, so they determine `ρ(V)`;
the local version `planarRhoLoc` is the value of `ρ(V)` at a configuration of the good event with
the same local data. It is measurable for the bonds inside the square of side `14 · 3ⁿ` around `V`
(`TriadicCube.planarLocalRegion`), so that local versions on cubes with disjoint regions are
independent, and every one is independent of the sum of the others over pairwise disjoint regions
(the form of independence used in the Chernoff bound `measureReal_sum_ge_le_of_bounded`). The
stationary version `planarRhoStat` is the local version at the cube of the same scale at the origin,
evaluated at the translated configuration; its law does not depend on the position of the cube.

Armstrong and Dario state the independence for all distinct subcubes, their local
quantities being measurable for the bonds inside the cube; here the local regions of neighbouring
cubes overlap, and independence holds for cubes whose regions are disjoint.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

variable {ω ω' : Configuration 2}

theorem toReal_planarNu_indicator (ω : Configuration 2) (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then ENNReal.ofReal (planarNu ω V ξ)
      else 0).toReal =
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarNu ω V ξ else 0 := by
  split_ifs
  · exact ENNReal.toReal_ofReal (planarNu_nonneg ξ)
  · rfl

theorem toReal_planarMu_indicator (ω : Configuration 2) (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then ENNReal.ofReal (-planarMu ω V q)
      else 0).toReal =
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V q else 0 := by
  split_ifs with hc
  · exact ENNReal.toReal_ofReal (neg_nonneg.2 (planarMu_nonpos hc.1 hc.2 q))
  · rfl

/-- `ρ` is determined by the indicators of `ν` and `-μ`. -/
theorem planarRho_eq_of_indicator_eq (p : unitInterval) {V V' : TriadicCube 2}
    (hν : ∀ ξ, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (planarNu ω V ξ) else 0) =
      if PlanarPartitionEvent ω' ∧ PlanarResolved ω' V' then
        ENNReal.ofReal (planarNu ω' V' ξ) else 0)
    (hμ : ∀ q, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (-planarMu ω V q) else 0) =
      if PlanarPartitionEvent ω' ∧ PlanarResolved ω' V' then
        ENNReal.ofReal (-planarMu ω' V' q) else 0) :
    planarRho p ω V = planarRho p ω' V' := by
  have hω : ∀ q, planarOmega p ω V q = planarOmega p ω' V' q := fun q => by
    have a := congrArg ENNReal.toReal (hν ((planarAhom p)⁻¹ *ᵥ q))
    have b := congrArg ENNReal.toReal (hμ q)
    rw [toReal_planarNu_indicator, toReal_planarNu_indicator] at a
    rw [toReal_planarMu_indicator, toReal_planarMu_indicator] at b
    simp only [planarOmega, a, b]
  unfold planarRho
  simp only [hω]

/-- On the good events, the local data determine `ρ(V)`. -/
theorem planarRho_eq_of_planarLocalData_eq (p : unitInterval) {V : TriadicCube 2}
    (hω : PlanarLocalGood ω V) (hω' : PlanarLocalGood ω' V)
    (h : planarLocalData ω V = planarLocalData ω' V) : planarRho p ω V = planarRho p ω' V :=
  planarRho_eq_of_indicator_eq p (planarNu_indicator_eq_of_planarLocalData_eq hω hω' h)
    (planarMu_indicator_eq_of_planarLocalData_eq hω hω' h)

/-- The value of `ρ(V)` at a configuration of the good event with given local data. -/
noncomputable def planarRhoLocOf (p : unitInterval) (V : TriadicCube 2) (t : PlanarLocalDatum V) :
    ℝ :=
  if h : ∃ ω, PlanarLocalGood ω V ∧ planarLocalData ω V = t then planarRho p h.choose V else 0

/-- **The local version of `ρ(V)`.** -/
noncomputable def planarRhoLoc (p : unitInterval) (V : TriadicCube 2) (ω : Configuration 2) : ℝ :=
  planarRhoLocOf p V (planarLocalData ω V)

/-- **Agreement with `ρ`** on the good event. -/
theorem planarRhoLoc_eq_of_good (p : unitInterval) {V : TriadicCube 2} (hω : PlanarLocalGood ω V) :
    planarRhoLoc p V ω = planarRho p ω V := by
  have hex : ∃ ω', PlanarLocalGood ω' V ∧ planarLocalData ω' V = planarLocalData ω V :=
    ⟨ω, hω, rfl⟩
  unfold planarRhoLoc planarRhoLocOf
  rw [dif_pos hex]
  exact planarRho_eq_of_planarLocalData_eq p hex.choose_spec.1 hω hex.choose_spec.2

theorem planarRhoLoc_nonneg (p : unitInterval) (V : TriadicCube 2) (ω : Configuration 2) :
    0 ≤ planarRhoLoc p V ω := by
  unfold planarRhoLoc planarRhoLocOf
  split_ifs
  · exact planarRho_nonneg _ _ _
  · exact le_rfl

theorem measurable_planarRhoLoc (p : unitInterval) (V : TriadicCube 2) :
    Measurable (planarRhoLoc p V) :=
  measurable_of_fiber_const (fun ω => planarLocalData ω V)
    (fun t => measurableSet_planarLocalData_eq V t) fun _ _ h => congrArg (planarRhoLocOf p V) h

/-- **Locality of `ρ_loc`**: it is measurable for the bonds inside the square of side `14 · 3ⁿ`
around `V`. -/
theorem measurable_planarRhoLoc_localBondSigma (p : unitInterval) (V : TriadicCube 2) :
    Measurable[localBondSigma V.planarLocalRegion] (planarRhoLoc p V) :=
  measurable_localBondSigma_of_eq _ (measurable_planarRhoLoc p V) fun _ _ h =>
    congrArg (planarRhoLocOf p V) (planarLocalData_eq_of_localBonds h).symm

theorem localBonds_mono {d : ℕ} {U W : Set (Vertex d)} (h : U ⊆ W) :
    localBonds U ⊆ localBonds W :=
  fun _ he x hx => h (he x hx)

/-- **Independence of local versions over pairwise disjoint regions**: for cubes with pairwise
disjoint local regions, a function of `ρ_loc` at one cube is independent of the sum of the same
function over any set of the others. -/
theorem indepFun_comp_planarRhoLoc_sum (p : unitInterval) {ι : Type*} (V : ι → TriadicCube 2)
    {g : ℝ → ℝ} (hg : Measurable g) {s : Finset ι}
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (V i).planarLocalRegion (V j).planarLocalRegion)
    {i : ι} (hi : i ∈ s) {T : Finset ι} (hT : T ⊆ s) (hiT : i ∉ T) :
    IndepFun (fun ω => g (planarRhoLoc p (V i) ω))
      (fun ω => ∑ j ∈ T, g (planarRhoLoc p (V j) ω)) (latticeBondLaw 2 p) := by
  set R : Set (Vertex 2) := ⋃ j ∈ T, (V j).planarLocalRegion with hR
  have hdR : Disjoint (V i).planarLocalRegion R := by
    rw [hR, Set.disjoint_iUnion_right]
    intro j
    rw [Set.disjoint_iUnion_right]
    intro hj
    exact hdisj i hi j (hT hj) fun h => hiT (h ▸ hj)
  have hmi : Measurable[localBondSigma (V i).planarLocalRegion]
      (fun ω => g (planarRhoLoc p (V i) ω)) :=
    hg.comp (measurable_planarRhoLoc_localBondSigma p (V i))
  have hmT : Measurable[localBondSigma R] (fun ω => ∑ j ∈ T, g (planarRhoLoc p (V j) ω)) := by
    refine measurable_localBondSigma_of_eq _ (Finset.measurable_sum T fun j _ =>
      hg.comp (measurable_planarRhoLoc p (V j))) fun ω ω' h => Finset.sum_congr rfl fun j hj => ?_
    have hsub : (V j).planarLocalRegion ⊆ R := by
      rw [hR]
      exact fun x hx => Set.mem_iUnion₂.2 ⟨j, hj, hx⟩
    exact congrArg (fun t => g (planarRhoLocOf p (V j) t))
      (planarLocalData_eq_of_localBonds fun e he => h e (localBonds_mono hsub he)).symm
  exact (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hdR) hmi.comap_le) hmT.comap_le)

/-- **The stationary local version of `ρ(V)`.** -/
noncomputable def planarRhoStat (p : unitInterval) (V : TriadicCube 2) (ω : Configuration 2) : ℝ :=
  planarRhoLoc p V.originCube (configurationTranslation (-V.center) ω)

/-- **Exact translation covariance.** -/
theorem planarRhoStat_shift (p : unitInterval) {V : TriadicCube 2} {z : Vertex 2}
    (hz : ∀ i, V.side ∣ z i) (ω : Configuration 2) :
    planarRhoStat p (V.shift z) (configurationTranslation z ω) = planarRhoStat p V ω := by
  unfold planarRhoStat
  rw [TriadicCube.originCube_shift, configurationTranslation_add, TriadicCube.center_shift_eq hz,
    neg_add, neg_add_cancel_right]

theorem measurable_planarRhoStat (p : unitInterval) (V : TriadicCube 2) :
    Measurable (planarRhoStat p V) :=
  (measurable_planarRhoLoc p _).comp (configurationTranslationMeasurableEquiv _).measurable

theorem planarRhoStat_nonneg (p : unitInterval) (V : TriadicCube 2) (ω : Configuration 2) :
    0 ≤ planarRhoStat p V ω :=
  planarRhoLoc_nonneg p _ _

/-- **Stationarity in law** of `ρ_stat` (Armstrong and Dario, (4.40), in dimension two). -/
theorem map_planarRhoStat_shift (p : unitInterval) {V : TriadicCube 2} {z : Vertex 2}
    (hz : ∀ i, V.side ∣ z i) :
    (latticeBondLaw 2 p).map (planarRhoStat p (V.shift z)) =
      (latticeBondLaw 2 p).map (planarRhoStat p V) := by
  have hmp := measurePreserving_configurationTranslation p z
  have h : planarRhoStat p V = planarRhoStat p (V.shift z) ∘ configurationTranslation z :=
    funext fun ω => (planarRhoStat_shift p hz ω).symm
  rw [h, ← Measure.map_map (measurable_planarRhoStat p _) hmp.measurable, hmp.map_eq]

/-- **Locality of `ρ_stat`.** -/
theorem measurable_planarRhoStat_localBondSigma (p : unitInterval) (V : TriadicCube 2) :
    Measurable[localBondSigma V.planarLocalRegion] (planarRhoStat p V) :=
  measurable_localBondSigma_of_eq _ (measurable_planarRhoStat p V) fun _ _ h =>
    congrArg (planarRhoLocOf p V.originCube)
      (planarLocalData_eq_of_localBonds (configurationTranslation_eq_on_localBonds h)).symm

/-- **Agreement with `ρ`** on the good event of the stationary versions. -/
theorem planarRhoStat_eq_of_good (p : unitInterval) {V : TriadicCube 2}
    (h : PlanarStatGood ω V) : planarRhoStat p V ω = planarRho p ω V := by
  unfold planarRhoStat
  rw [planarRhoLoc_eq_of_good p h.2]
  have hω : configurationTranslation V.center (configurationTranslation (-V.center) ω) = ω := by
    rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]
  have h2 : PlanarLocalGood (configurationTranslation V.center
      (configurationTranslation (-V.center) ω)) (V.originCube.shift V.center) := by
    rw [hω, V.originCube_shift_center]
    exact h.1
  have hν := planarNu_indicator_shift_eq_of_good V.originCube_side_dvd_center h.2 h2
  have hμ := planarMu_indicator_shift_eq_of_good V.originCube_side_dvd_center h.2 h2
  rw [hω, V.originCube_shift_center] at hν hμ
  exact (planarRho_eq_of_indicator_eq p hν hμ).symm

/-- **Independence of stationary local versions over pairwise disjoint regions.** -/
theorem indepFun_comp_planarRhoStat_sum (p : unitInterval) {ι : Type*} (V : ι → TriadicCube 2)
    {g : ℝ → ℝ} (hg : Measurable g) {s : Finset ι}
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (V i).planarLocalRegion (V j).planarLocalRegion)
    {i : ι} (hi : i ∈ s) {T : Finset ι} (hT : T ⊆ s) (hiT : i ∉ T) :
    IndepFun (fun ω => g (planarRhoStat p (V i) ω))
      (fun ω => ∑ j ∈ T, g (planarRhoStat p (V j) ω)) (latticeBondLaw 2 p) := by
  set R : Set (Vertex 2) := ⋃ j ∈ T, (V j).planarLocalRegion with hR
  have hdR : Disjoint (V i).planarLocalRegion R := by
    rw [hR, Set.disjoint_iUnion_right]
    intro j
    rw [Set.disjoint_iUnion_right]
    intro hj
    exact hdisj i hi j (hT hj) fun h => hiT (h ▸ hj)
  have hmi : Measurable[localBondSigma (V i).planarLocalRegion]
      (fun ω => g (planarRhoStat p (V i) ω)) :=
    hg.comp (measurable_planarRhoStat_localBondSigma p (V i))
  have hmT : Measurable[localBondSigma R] (fun ω => ∑ j ∈ T, g (planarRhoStat p (V j) ω)) := by
    refine measurable_localBondSigma_of_eq _ (Finset.measurable_sum T fun j _ =>
      hg.comp (measurable_planarRhoStat p (V j))) fun ω ω' h => Finset.sum_congr rfl fun j hj => ?_
    have hsub : (V j).planarLocalRegion ⊆ R := by
      rw [hR]
      exact fun x hx => Set.mem_iUnion₂.2 ⟨j, hj, hx⟩
    exact congrArg (fun t => g (planarRhoLocOf p (V j).originCube t))
      (planarLocalData_eq_of_localBonds (configurationTranslation_eq_on_localBonds
        fun e he => h e (localBonds_mono hsub he))).symm
  exact (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hdR) hmi.comap_le) hmT.comap_le)

end Rigidity.Proofs.Cluster
