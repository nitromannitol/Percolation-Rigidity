import Rigidity.Percolation.Bootstrap.Transport
import Rigidity.Percolation.Bootstrap.Relay

/-!
# Exploring a sprinkled cluster towards a target

The sprinkled cluster of `S` inside `W` is determined by the bonds internal to `W`. If `S` is
joined inside `W` to a target `T₁` at level `p₀` with probability close to one, then, conditioned
on the cut from `S` inside its zone being closed at level `p₀`, its sprinkled cluster meets `T₁`
with conditional probability close to one. A vertex of the sprinkled cluster far from `S` carries
a seed path of the cluster. Per-side failure bounds for the two explorations combine into the
failure bound of the two-chances step, the two sides being independent.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

variable {d : ℕ}

/-- A seed path whose cube lies in a zone is a seed path of the trace in the zone. -/
theorem HasSeedPath.inter {S Z : Set (Vertex d)} {s : Vertex d} {u : ℕ}
    (h : HasSeedPath S s u) (hZ : cubeAt s u ⊆ Z) : HasSeedPath (S ∩ Z) s u := by
  obtain ⟨hs, v, hv, hr⟩ := h
  refine ⟨Set.mem_inter hs (hZ (show s ∈ cubeAt s u from fun i => by simp)), v, hv, ?_⟩
  refine reachable_openIn_mono (fun x hx => ?_) hr
  exact ⟨⟨hx.1, hZ hx.2⟩, hx.2⟩

/-- A vertex of the sprinkled cluster whose cube misses `S` carries a seed path of the
cluster. -/
theorem hasSeedPath_sprinkledCluster {p₀ q : unitInterval} {S W : Finset (Vertex d)}
    (hSW : S ⊆ W) {ω : BondMarks d} {z : Vertex d} (hz : z ∈ sprinkledCluster p₀ q S W ω)
    {u : ℕ} (hfar : ∀ g ∈ S, g ∉ cubeAt z u) :
    HasSeedPath (sprinkledCluster p₀ q S W ω : Set (Vertex d)) z u := by
  refine hasSeedPath_of_connected (γ := S) (fun z' hz' => ?_) hz hfar
  obtain ⟨g, hg, hgz⟩ := reachable_of_mem_clusterWith _ hSW hz'
  exact ⟨g, hg, hgz.mono (openIn_mono_configuration (fun _ => Bool.le_true _) _)⟩

/-- Every property of the sprinkled cluster inside `W` is determined by the bonds internal to
`W`. -/
theorem measurableSet_sprinkledCluster_pred (p₀ q : unitInterval) {S W : Finset (Vertex d)}
    (hSW : S ⊆ W) (P : Finset (Vertex d) → Prop) :
    MeasurableSet[bondMarkSigma (localBonds (W : Set (Vertex d)))]
      {ω | P (sprinkledCluster p₀ q S W ω)} := by
  classical
  have heq : {ω | P (sprinkledCluster p₀ q S W ω)} =
      ⋃ c ∈ W.powerset.filter (fun c => S ⊆ c ∧ P c), {ω | sprinkledCluster p₀ q S W ω = c} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨clusterWith_subset _ _ _ ω, subset_clusterWith _ hSW ω, h⟩, rfl⟩
    · rintro ⟨c, ⟨-, -, hc⟩, rfl⟩
      exact hc
  rw [heq]
  refine Finset.measurableSet_biUnion _ fun c hc => ?_
  obtain ⟨hcW, hSc, -⟩ := Finset.mem_filter.1 hc
  have hcW' : c ⊆ W := Finset.mem_powerset.1 hcW
  have h1 : {ω | sprinkledCluster p₀ q S W ω = c} =
      genWith (sprinkleLevel p₀ q S W) S c ∩
        bondMarksAbove (vertexCutBondsIn c (W : Set (Vertex d))) (sprinkleLevel p₀ q S W) := by
    ext ω
    exact clusterWith_eq_iff _ hSc hcW' ω
  rw [h1]
  refine MeasurableSet.inter ?_ ?_
  · refine bondMarkSigma_mono (fun e he x hx => ?_) _ (measurableSet_genWith _ S c)
    exact Finset.mem_coe.2 (hcW' (he x hx))
  · exact bondMarkSigma_mono (fun e he => mem_localBonds_of_mem_vertexCutBondsIn
      (Finset.mem_coe.1 he)) _ (measurableSet_bondMarksAbove_local _ _)

/-- A closed cut inside a zone of `W` is determined by the bonds internal to `W`. -/
theorem measurableSet_cutClosed_local (p : unitInterval) {S Z W : Finset (Vertex d)}
    (hZW : Z ⊆ W) :
    MeasurableSet[bondMarkSigma (localBonds (W : Set (Vertex d)))] (cutClosed p S Z) := by
  refine bondMarkSigma_mono (fun e he x hx => ?_) _ (measurableSet_bondMarksAbove_local _ _)
  exact Finset.mem_coe.2 (hZW (mem_localBonds_of_mem_vertexCutBondsIn (Finset.mem_coe.1 he) x hx))

/-- **The sprinkled cluster reaches a target.** Conditioned on the cut from `S` inside its zone
being closed at level `p₀`, the sprinkled cluster of `S` inside `W` at level `p₀ + δ` misses a
target `T₁` with conditional probability at most `P_{p₀}(S ↮ T₁ in W) / (1 - p₀)^K + (1 - δ)^K`.
The bound is stated before division by the probability of the conditioning. -/
theorem sprinkledCluster_reach_le (p₀ : unitInterval) (hp₀ : (p₀ : ℝ) < 1) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : (p₀ : ℝ) + δ ≤ 1) {S ZS WS : Finset (Vertex d)} (hSZ : S ⊆ ZS)
    (hZW : ZS ⊆ WS) (T₁ : Finset (Vertex d)) (K : ℕ) :
    (bondMarkLaw d).real (cutClosed p₀ S ZS ∩
        {ω | ¬ ∃ z ∈ T₁, z ∈ sprinkledCluster p₀ (raisedLevel p₀ δ hδ.le hδ1) S WS ω}) ≤
      ((latticeBondLaw d p₀).real {η | ¬ ∃ x ∈ S, ∃ z ∈ T₁,
          z ∈ (WS : Set (Vertex d)) \ (S : Set (Vertex d)) ∧ (openIn η WS).Reachable x z} /
          (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K) *
        (bondMarkLaw d).real (cutClosed p₀ S ZS) := by
  classical
  set q := raisedLevel p₀ δ hδ.le hδ1 with hq
  have hpq : p₀ ≤ q := by
    change (p₀ : ℝ) ≤ (p₀ : ℝ) + δ
    linarith
  have hSW : S ⊆ WS := hSZ.trans hZW
  have hF₀ : vertexCutBondsIn S (ZS : Set (Vertex d)) ⊆ vertexCutBondsIn S (WS : Set (Vertex d)) := by
    intro e he
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 he
    exact Finset.mem_filter.2 ⟨h1, fun x hx => Finset.mem_coe.2 (hZW (h2 x hx))⟩
  have hpart := bondMarkLaw_real_partialCut_inter_not_exitOpens_le p₀ hp₀ δ hδ hδ1 S WS T₁
    (fun x hx => hSW hx) (vertexCutBondsIn S (ZS : Set (Vertex d))) hF₀ K
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hpart
  rintro ω ⟨hH, hmiss⟩
  refine ⟨hH, fun hexit => hmiss ?_⟩
  obtain ⟨e, he, hle⟩ := hexit
  obtain ⟨heF, x, hx, y, hy, hxy, rfl, z, hzT, hz, hreach⟩ :=
    (mem_boundaryCandidateBonds _ _ _ _ _ _).1 he
  have hle' : ω (bondOfAdjacent hxy) ≤ q := by
    have h := hle
    simp only [raisedBondThreshold, he, ↓reduceIte, constThreshold] at h
    exact h
  refine ⟨z, hzT, Finset.mem_filter.2 ⟨Finset.mem_coe.1 hz.1, x, hx, ?_⟩⟩
  have hopen : thresholdWith (sprinkleLevel p₀ q S WS) ω (bondOfAdjacent hxy) = true := by
    change markThreshold (sprinkleLevel p₀ q S WS (bondOfAdjacent hxy))
      (ω (bondOfAdjacent hxy)) = true
    simp only [sprinkleLevel, heF, ↓reduceIte, markThreshold, hle']
  have hedge : (openIn (thresholdWith (sprinkleLevel p₀ q S WS) ω) WS).Adj x y :=
    ⟨(openGraph_adj_iff _ x y).2 ⟨hxy, hopen⟩, hSW hx, hy.1⟩
  have hge : ∀ e', constThreshold p₀ e' ≤ sprinkleLevel p₀ q S WS e' := by
    intro e'
    unfold sprinkleLevel constThreshold
    split_ifs
    · exact hpq
    · exact le_rfl
  have htail : (openIn (thresholdWith (sprinkleLevel p₀ q S WS) ω) WS).Reachable y z :=
    openIn_reachable_mono_region Set.sdiff_subset
      (hreach.mono (openIn_mono_configuration (thresholdWith_mono hge ω) _))
  exact hedge.reachable.trans htail

/-- **Combining the two sides.** Per-side failure bounds for the admissibility of the traces of
the two sprinkled clusters give the failure bound of the two-chances step. -/
theorem twoSided_failure_le (p₀ q : unitInterval) {S T ZS ZT WS WT : Finset (Vertex d)}
    (hSZ : S ⊆ ZS) (hZWS : ZS ⊆ WS) (hTZ : T ⊆ ZT) (hZWT : ZT ⊆ WT) (hWW : Disjoint WS WT)
    (ZL ZR : Bool → Finset (Vertex d)) (AdmL AdmR : Bool → Finset (Vertex d) → Prop)
    {εS εT : ℝ}
    (hFS : ∀ k, (bondMarkLaw d).real (cutClosed p₀ S ZS ∩
        {ω | ¬ AdmL k (sprinkledCluster p₀ q S WS ω ∩ ZL k)}) ≤
        εS * (bondMarkLaw d).real (cutClosed p₀ S ZS))
    (hFT : ∀ k, (bondMarkLaw d).real (cutClosed p₀ T ZT ∩
        {ω | ¬ AdmR k (sprinkledCluster p₀ q T WT ω ∩ ZR k)}) ≤
        εT * (bondMarkLaw d).real (cutClosed p₀ T ZT)) :
    (bondMarkLaw d).real ((cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT) ∩
        {ω | ¬ ∀ k, AdmL k (sprinkledCluster p₀ q S WS ω ∩ ZL k) ∧
          AdmR k (sprinkledCluster p₀ q T WT ω ∩ ZR k)}) ≤
      (2 * εS + 2 * εT) * (bondMarkLaw d).real (cutClosed p₀ S ZS ∩ cutClosed p₀ T ZT) := by
  classical
  set μ := bondMarkLaw d with hμ
  set HS := cutClosed p₀ S ZS with hHS
  set HT := cutClosed p₀ T ZT with hHT
  have hdisj := disjoint_localBonds (Finset.disjoint_coe.2 hWW)
  have hHSm : MeasurableSet[bondMarkSigma (localBonds (WS : Set (Vertex d)))] HS :=
    measurableSet_cutClosed_local p₀ hZWS
  have hHTm : MeasurableSet[bondMarkSigma (localBonds (WT : Set (Vertex d)))] HT :=
    measurableSet_cutClosed_local p₀ hZWT
  set BS : Bool → Set (BondMarks d) := fun k =>
    {ω | ¬ AdmL k (sprinkledCluster p₀ q S WS ω ∩ ZL k)} with hBS
  set BT : Bool → Set (BondMarks d) := fun k =>
    {ω | ¬ AdmR k (sprinkledCluster p₀ q T WT ω ∩ ZR k)} with hBT
  have hBSm : ∀ k, MeasurableSet[bondMarkSigma (localBonds (WS : Set (Vertex d)))] (BS k) :=
    fun k => measurableSet_sprinkledCluster_pred p₀ q (hSZ.trans hZWS)
      (fun c => ¬ AdmL k (c ∩ ZL k))
  have hBTm : ∀ k, MeasurableSet[bondMarkSigma (localBonds (WT : Set (Vertex d)))] (BT k) :=
    fun k => measurableSet_sprinkledCluster_pred p₀ q (hTZ.trans hZWT)
      (fun c => ¬ AdmR k (c ∩ ZR k))
  have hprod : μ.real (HS ∩ HT) = μ.real HS * μ.real HT :=
    bondMarkLaw_real_inter_of_disjoint hdisj hHSm hHTm
  have hSk : ∀ k, μ.real ((HS ∩ HT) ∩ BS k) ≤ εS * μ.real (HS ∩ HT) := by
    intro k
    have heq : (HS ∩ HT) ∩ BS k = (HS ∩ BS k) ∩ HT := by
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [heq, bondMarkLaw_real_inter_of_disjoint hdisj (hHSm.inter (hBSm k)) hHTm, hprod]
    have := hFS k
    calc μ.real (HS ∩ BS k) * μ.real HT ≤ (εS * μ.real HS) * μ.real HT :=
          mul_le_mul_of_nonneg_right this measureReal_nonneg
      _ = εS * (μ.real HS * μ.real HT) := by ring
  have hTk : ∀ k, μ.real ((HS ∩ HT) ∩ BT k) ≤ εT * μ.real (HS ∩ HT) := by
    intro k
    have heq : (HS ∩ HT) ∩ BT k = HS ∩ (HT ∩ BT k) := by
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [heq, bondMarkLaw_real_inter_of_disjoint hdisj hHSm (hHTm.inter (hBTm k)), hprod]
    have := hFT k
    calc μ.real HS * μ.real (HT ∩ BT k) ≤ μ.real HS * (εT * μ.real HT) :=
          mul_le_mul_of_nonneg_left this measureReal_nonneg
      _ = εT * (μ.real HS * μ.real HT) := by ring
  have hsub : (HS ∩ HT) ∩ {ω | ¬ ∀ k, AdmL k (sprinkledCluster p₀ q S WS ω ∩ ZL k) ∧
      AdmR k (sprinkledCluster p₀ q T WT ω ∩ ZR k)} ⊆
      (((HS ∩ HT) ∩ BS true) ∪ ((HS ∩ HT) ∩ BS false)) ∪
        (((HS ∩ HT) ∩ BT true) ∪ ((HS ∩ HT) ∩ BT false)) := by
    rintro ω ⟨hω, hbad⟩
    simp only [Set.mem_setOf_eq, not_forall, not_and_or] at hbad
    obtain ⟨k, hk | hk⟩ := hbad
    · cases k
      · exact Or.inl (Or.inr ⟨hω, hk⟩)
      · exact Or.inl (Or.inl ⟨hω, hk⟩)
    · cases k
      · exact Or.inr (Or.inr ⟨hω, hk⟩)
      · exact Or.inr (Or.inl ⟨hω, hk⟩)
  calc _ ≤ μ.real ((((HS ∩ HT) ∩ BS true) ∪ ((HS ∩ HT) ∩ BS false)) ∪
        (((HS ∩ HT) ∩ BT true) ∪ ((HS ∩ HT) ∩ BT false))) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (μ.real ((HS ∩ HT) ∩ BS true) + μ.real ((HS ∩ HT) ∩ BS false)) +
        (μ.real ((HS ∩ HT) ∩ BT true) + μ.real ((HS ∩ HT) ∩ BT false)) :=
        (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _)
          (measureReal_union_le _ _))
    _ ≤ (εS * μ.real (HS ∩ HT) + εS * μ.real (HS ∩ HT)) +
        (εT * μ.real (HS ∩ HT) + εT * μ.real (HS ∩ HT)) :=
        add_le_add (add_le_add (hSk true) (hSk false)) (add_le_add (hTk true) (hTk false))
    _ = (2 * εS + 2 * εT) * μ.real (HS ∩ HT) := by ring

end Rigidity.Percolation
