import Rigidity.Proofs.S2.ClusterDensityMean

/-!
# A single bond and the infinite-cluster density

Resampling one bond makes the two open graphs comparable. Consequently their infinite-cluster
traces in a finite cube are nested, and the absolute change in the count is the size of their
symmetric difference.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- Resample a single bond from a second configuration. -/
noncomputable def resampleBond (ω η : Configuration d) (e : Bond d) : Configuration d := by
  classical
  exact fun f => if f = e then η e else ω f

/-- Pointwise inclusion of open bonds implies graph inclusion. -/
theorem openGraph_le_of_bonds {ω η : Configuration d}
    (h : ∀ e, ω e = true → η e = true) : openGraph ω ≤ openGraph η := by
  intro x y hxy
  obtain ⟨hxy, hopen⟩ := hxy
  exact ⟨hxy, h _ hopen⟩

/-- Resampling one bond makes the original and resampled open graphs comparable. -/
theorem openGraph_resampleBond_comparable (ω η : Configuration d) (e : Bond d) :
    openGraph ω ≤ openGraph (resampleBond ω η e) ∨
      openGraph (resampleBond ω η e) ≤ openGraph ω := by
  classical
  by_cases he : ω e = true
  · right
    apply openGraph_le_of_bonds
    intro f hf
    by_cases hfe : f = e
    · simpa only [hfe] using he
    · simpa only [resampleBond, hfe, ↓reduceIte] using hf
  · left
    apply openGraph_le_of_bonds
    intro f hf
    by_cases hfe : f = e
    · subst f
      exact (he hf).elim
    · simpa only [resampleBond, hfe, ↓reduceIte] using hf

/-- Infinite-component membership is increasing under graph inclusion. -/
theorem infiniteComponentEvent_mono {ω η : Configuration d} (h : openGraph ω ≤ openGraph η)
    (x : Vertex d) (hx : ω ∈ infiniteComponentEvent x) : η ∈ infiniteComponentEvent x := by
  rw [mem_infiniteComponentEvent_iff] at hx ⊢
  intro S
  obtain ⟨y, hy, hxy⟩ := hx S
  exact ⟨y, hy, SimpleGraph.Reachable.mono h hxy⟩

/-- The vertices in a triadic cube belonging to infinite open components. -/
noncomputable def infiniteClusterTrace (m : ℕ) (k : Vertex d) (ω : Configuration d) :
    Finset (Vertex d) := by
  classical
  exact (triadicCubeFinset d m k).filter fun y => ω ∈ infiniteComponentEvent y

/-- The trace cardinality is the infinite-cluster count. -/
theorem card_infiniteClusterTrace (m : ℕ) (k : Vertex d) (ω : Configuration d) :
    (infiniteClusterTrace m k ω).card = infiniteClusterCount (triadicCube d m k) ω := by
  classical
  exact (infiniteClusterCount_triadicCube m k ω).symm

/-- Graph inclusion nests the infinite-cluster traces. -/
theorem infiniteClusterTrace_mono {ω η : Configuration d} (h : openGraph ω ≤ openGraph η)
    (m : ℕ) (k : Vertex d) : infiniteClusterTrace m k ω ⊆ infiniteClusterTrace m k η := by
  classical
  intro x hx
  simp only [infiniteClusterTrace, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, infiniteComponentEvent_mono h x hx.2⟩

/-- For nested finite sets, the absolute cardinality difference is the size of the difference. -/
theorem abs_card_sub_eq_card_sdiff {α : Type*} [DecidableEq α] {S T : Finset α} (hST : S ⊆ T) :
    |(S.card : ℝ) - T.card| = ((T \ S).card : ℝ) := by
  have hc : S.card ≤ T.card := Finset.card_le_card hST
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hc)), Finset.card_sdiff,
    Finset.inter_eq_left.mpr hST, Nat.cast_sub hc]

/-- Resampling one bond changes the cluster count by the size of the symmetric-difference trace. -/
theorem abs_infiniteClusterCount_resampleBond (m : ℕ) (k : Vertex d)
    (ω η : Configuration d) (e : Bond d) :
    |(infiniteClusterCount (triadicCube d m k) ω : ℝ) -
      (infiniteClusterCount (triadicCube d m k) (resampleBond ω η e) : ℝ)| =
      (((infiniteClusterTrace m k ω \ infiniteClusterTrace m k (resampleBond ω η e)) ∪
        (infiniteClusterTrace m k (resampleBond ω η e) \ infiniteClusterTrace m k ω)).card : ℝ) := by
  classical
  rw [← card_infiniteClusterTrace m k ω, ← card_infiniteClusterTrace m k (resampleBond ω η e)]
  rcases openGraph_resampleBond_comparable ω η e with h | h
  · have hsub := infiniteClusterTrace_mono h m k
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.empty_union]
    exact abs_card_sub_eq_card_sdiff hsub
  · have hsub := infiniteClusterTrace_mono h m k
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.union_empty, abs_sub_comm]
    exact abs_card_sub_eq_card_sdiff hsub

/-- Resampling preserves every bond other than the selected bond. -/
theorem resampleBond_apply_of_ne (ω η : Configuration d) (e f : Bond d) (h : f ≠ e) :
    resampleBond ω η e f = ω f := by
  classical
  simp only [resampleBond, h, ↓reduceIte]

/-- If a vertex becomes infinite after changing one bond, it reaches an endpoint in the
configuration where its component was finite. -/
theorem newly_infinite_reaches_changedBond {ω η : Configuration d} (e : Bond d)
    (hagrees : ∀ f : Bond d, f ≠ e → ω f = η f) (x : Vertex d)
    (hnew : η ∈ infiniteComponentEvent x) (hold : ω ∉ infiniteComponentEvent x) :
    ∃ y ∈ e.val, (openGraph ω).Reachable x y := by
  classical
  by_contra hno
  push Not at hno
  have hclosed : ∀ {u v : Vertex d}, (openGraph ω).Reachable x u →
      (openGraph η).Adj u v → (openGraph ω).Reachable x v := by
    intro u v hxu huv
    by_cases huv' : (openGraph ω).Adj u v
    · exact hxu.trans huv'.reachable
    · obtain ⟨hadj, hopen⟩ := huv
      have heq : bondOfAdjacent hadj = e := by
        by_contra hne
        have he := hagrees (bondOfAdjacent hadj) hne
        apply huv'
        exact ⟨hadj, he.trans hopen⟩
      have hu : u ∈ e.val := by
        rw [← congrArg Subtype.val heq]
        simp [bondOfAdjacent]
      exact (hno u hu hxu).elim
  have hwalk : ∀ {u v : Vertex d} (P : (openGraph η).Walk u v),
      (openGraph ω).Reachable x u → (openGraph ω).Reachable x v := by
    intro u v P
    induction P with
    | nil => exact fun h => h
    | cons huv P ih => exact fun h => ih (hclosed h huv)
  apply hold
  rw [mem_infiniteComponentEvent_iff] at hnew ⊢
  intro S
  obtain ⟨y, hy, ⟨P⟩⟩ := hnew S
  exact ⟨y, hy, hwalk P (SimpleGraph.Reachable.refl _)⟩

/-- A vertex lost from the infinite cluster by resampling reaches the selected bond in the
configuration where its component is finite. -/
theorem lost_vertex_reaches_resampledBond (ω η : Configuration d) (e : Bond d) (x : Vertex d)
    (hOld : ω ∈ infiniteComponentEvent x)
    (hNew : resampleBond ω η e ∉ infiniteComponentEvent x) :
    ∃ y ∈ e.val, (openGraph (resampleBond ω η e)).Reachable x y :=
  newly_infinite_reaches_changedBond e
    (fun f hf => (resampleBond_apply_of_ne ω η e f hf)) x hOld hNew

/-- A vertex gained by the infinite cluster after resampling reaches the selected bond in the
configuration where its component is finite. -/
theorem gained_vertex_reaches_resampledBond (ω η : Configuration d) (e : Bond d) (x : Vertex d)
    (hNew : resampleBond ω η e ∈ infiniteComponentEvent x)
    (hOld : ω ∉ infiniteComponentEvent x) :
    ∃ y ∈ e.val, (openGraph ω).Reachable x y :=
  newly_infinite_reaches_changedBond e
    (fun f hf => (resampleBond_apply_of_ne ω η e f hf).symm) x hNew hOld

/-- A vertex reachable from a finite component belongs to a finite component. -/
theorem finite_component_of_reachable {ω : Configuration d} {x y : Vertex d}
    (hxy : (openGraph ω).Reachable x y) (hx : ω ∉ infiniteComponentEvent x) :
    ((openGraph ω).connectedComponentMk y).supp.Finite := by
  have hfin : ((openGraph ω).connectedComponentMk x).supp.Finite := Set.not_infinite.mp hx
  rw [SimpleGraph.ConnectedComponent.sound hxy] at hfin
  exact hfin

/-- Every vertex lost under single-bond resampling reaches a finite component at the bond. -/
theorem lost_vertex_reaches_finite_component (ω η : Configuration d) (e : Bond d) (x : Vertex d)
    (hOld : ω ∈ infiniteComponentEvent x)
    (hNew : resampleBond ω η e ∉ infiniteComponentEvent x) :
    ∃ y ∈ e.val, (openGraph (resampleBond ω η e)).Reachable x y ∧
      ((openGraph (resampleBond ω η e)).connectedComponentMk y).supp.Finite := by
  obtain ⟨y, hy, hxy⟩ := lost_vertex_reaches_resampledBond ω η e x hOld hNew
  exact ⟨y, hy, hxy, finite_component_of_reachable hxy hNew⟩

/-- Every vertex gained under single-bond resampling reaches a finite component at the bond. -/
theorem gained_vertex_reaches_finite_component (ω η : Configuration d) (e : Bond d) (x : Vertex d)
    (hNew : resampleBond ω η e ∈ infiniteComponentEvent x)
    (hOld : ω ∉ infiniteComponentEvent x) :
    ∃ y ∈ e.val, (openGraph ω).Reachable x y ∧
      ((openGraph ω).connectedComponentMk y).supp.Finite := by
  obtain ⟨y, hy, hxy⟩ := gained_vertex_reaches_resampledBond ω η e x hNew hOld
  exact ⟨y, hy, hxy, finite_component_of_reachable hxy hOld⟩

/-- A changed trace vertex belongs to a finite component touching the resampled bond. -/
theorem changed_trace_vertex_reaches_finite_component (m : ℕ) (k : Vertex d)
    (ω η : Configuration d) (e : Bond d) {x : Vertex d}
    (hx : x ∈ (infiniteClusterTrace m k ω \ infiniteClusterTrace m k (resampleBond ω η e)) ∪
      (infiniteClusterTrace m k (resampleBond ω η e) \ infiniteClusterTrace m k ω)) :
    (∃ y ∈ e.val, (openGraph ω).Reachable x y ∧
        ((openGraph ω).connectedComponentMk y).supp.Finite) ∨
      (∃ y ∈ e.val, (openGraph (resampleBond ω η e)).Reachable x y ∧
        ((openGraph (resampleBond ω η e)).connectedComponentMk y).supp.Finite) := by
  classical
  simp only [Finset.mem_union, Finset.mem_sdiff, infiniteClusterTrace, Finset.mem_filter] at hx
  rcases hx with ⟨⟨hxQ, hOld⟩, hNot⟩ | ⟨⟨hxQ, hNew⟩, hNot⟩
  · right
    apply lost_vertex_reaches_finite_component ω η e x hOld
    intro hNew
    exact hNot ⟨hxQ, hNew⟩
  · left
    apply gained_vertex_reaches_finite_component ω η e x hNew
    intro hOld
    exact hNot ⟨hxQ, hOld⟩

end Rigidity.Proofs.S2
