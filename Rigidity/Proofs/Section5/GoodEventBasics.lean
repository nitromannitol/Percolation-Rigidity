import Rigidity.Steps.Section5.GoodEventLowerBound
import Rigidity.Steps.Section5.PrintedGoodEvents
import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation

/-!
# Lemmas 5.25 and 5.26: translation covariance of the good event and the first good event

Two steps of the carvings of Lemmas 5.25 and 5.26 (`Rigidity.Steps.Section5`, corrected draft
L2337-2406). No literature input is used.

* `goodEventTranslationStep` (stationarity, L2381): `ω ∈ G(x, C_χ, K)` if and only if
  `τ_{-x} ω ∈ G(0, C_χ, K)`. The translation `τ_z` moves the open graph by `z`, hence the infinite
  cluster (`openComponentTranslation_uniqueInfiniteComponent`) together with its graph structure
  (`openComponentTranslationIso`), the connected subsets and the disjoint paths to infinity of
  the event `E_R`, the paths of `G_1`, and the corrected planes of `G_2` and `G_3`
  (`isCorrectedPlane_translation_iff`). Each event is moved in one direction by every `z`
  (`eventE_translation`, `eventG1_translation`, `eventG2_translation`, `eventG3_translation`);
  the converse is the translation by `-z`.
* `firstGoodEventStep` (eq. `PG1goesto1`, corrected): the infinite cluster is connected and its
  support is infinite, so a path of the cluster from the origin reaches a site `y` with
  `|y|₁ ≥ K`. If `G_1(0, K)` fails, this path has fewer than `c₁ |y|₁` sites in `E_R`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

variable {ω : Configuration 2}

/-! ### Translation covariance -/

section Translation

variable (z : Vertex 2) (C : OpenComponent ω)

/-- `y - z ∈ Q_r(x)` if and only if `y ∈ Q_r(x + z)`. -/
theorem sub_mem_cubeAt_iff (x y : Vertex 2) (r : ℕ) :
    y - z ∈ cubeAt x r ↔ y ∈ cubeAt (x + z) r := by
  simp only [cubeAt, Set.mem_setOf_eq]
  exact forall_congr' fun i => by rw [Pi.sub_apply, Pi.add_apply, sub_sub, add_comm (z i)]

/-- Connected sets of the translated cluster pull back to connected sets of the cluster. -/
theorem isConnectedSet_preimage_translation {S : Set (openComponentTranslation z ω C)}
    (hS : IsConnectedSet _ S) :
    IsConnectedSet C (openComponentTranslationIso z C ⁻¹' S) := by
  set φ := openComponentTranslationIso z C
  intro a ha b hb
  obtain ⟨hxa, hxb, hr⟩ := hS (φ a) ha (φ b) hb
  have hφ : Set.MapsTo φ.symm S (φ ⁻¹' S) := fun y hy => by
    simpa only [Set.mem_preimage, RelIso.apply_symm_apply] using hy
  have hmap := SimpleGraph.Reachable.map (SimpleGraph.induceHom φ.symm.toHom hφ) hr
  have e : ∀ (c : C) (hc : φ c ∈ S), SimpleGraph.induceHom φ.symm.toHom hφ ⟨φ c, hc⟩ =
      ⟨c, hc⟩ := fun c _ => Subtype.ext (φ.symm_apply_apply c)
  rw [e a ha, e b hb] at hmap
  exact ⟨ha, hb, hmap⟩

/-- Disjoint paths to infinity of the cluster push forward to the translated cluster. -/
theorem hasDisjointPathsToInfinity_translation {S : Set (openComponentTranslation z ω C)}
    {k : ℕ} (hS : HasDisjointPathsToInfinity C (openComponentTranslationIso z C ⁻¹' S) k) :
    HasDisjointPathsToInfinity _ S k := by
  set φ := openComponentTranslationIso z C
  obtain ⟨γ, hγ, hdisj⟩ := hS
  refine ⟨fun j n => φ (γ j n), fun j => ⟨⟨φ.injective.comp (hγ j).1.1,
    fun n => φ.map_adj_iff.mpr ((hγ j).1.2.1 n), fun _ => trivial⟩, (hγ j).2⟩,
    fun j j' hjj' => Set.disjoint_left.mpr ?_⟩
  rintro _ ⟨n, rfl⟩ ⟨m, hm⟩
  exact Set.disjoint_left.mp (hdisj j j' hjj') ⟨n, rfl⟩ ⟨m, φ.injective hm⟩

variable {C}

/-- Corrected planes of the translated cluster pull back to corrected planes of the cluster. -/
theorem isCorrectedPlane_comp_translation {q : Fin 2 → ℝ}
    {ℓ : openComponentTranslation z ω C → ℝ} (hℓ : IsCorrectedPlane _ q ℓ) :
    IsCorrectedPlane C q fun y => ℓ (openComponentTranslationIso z C y) := by
  refine (isCorrectedPlane_translation_iff z C q _).mp ?_
  convert hℓ using 2 with y
  exact congrArg ℓ ((openComponentTranslationIso z C).apply_symm_apply y)

end Translation

variable {Cf : ℕ} {R c₁ Cχ K : ℝ}

/-- The event `E_R` moves with the environment: `ω ∈ E_R(y)` implies `τ_z ω ∈ E_R(y + z)`. -/
theorem eventE_translation (z : Vertex 2) {y : Vertex 2} (hω : ω ∈ eventE Cf R y) :
    configurationTranslation z ω ∈ eventE Cf R (y + z) := by
  intro h'
  have h := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mp h'
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  rw [← hC]
  intro S hfin hconn hy hdiam
  set φ := openComponentTranslationIso z (uniqueInfiniteComponent h)
  refine hasDisjointPathsToInfinity_translation z _ (hω h (φ ⁻¹' S)
    (hfin.preimage φ.injective.injOn) (isConnectedSet_preimage_translation z _ hconn) ?_ ?_)
  · obtain ⟨a, ha, hav⟩ := hy
    refine ⟨φ.symm a, by simpa only [Set.mem_preimage, RelIso.apply_symm_apply] using ha, ?_⟩
    rw [openComponentTranslationIso_symm_val, hav, add_sub_cancel_right]
  · obtain ⟨a, ha, b, hb, hab⟩ := hdiam
    refine ⟨φ.symm a, by simpa only [Set.mem_preimage, RelIso.apply_symm_apply] using ha,
      φ.symm b, by simpa only [Set.mem_preimage, RelIso.apply_symm_apply] using hb, ?_⟩
    rwa [openComponentTranslationIso_symm_val, openComponentTranslationIso_symm_val,
      sub_sub_sub_cancel_right]

/-- `τ_z ω ∈ E_R(y + z)` if and only if `ω ∈ E_R(y)`. -/
theorem translation_mem_eventE_iff (z y : Vertex 2) :
    configurationTranslation z ω ∈ eventE Cf R (y + z) ↔ ω ∈ eventE Cf R y := by
  refine ⟨fun h => ?_, eventE_translation z⟩
  have := eventE_translation (-z) h
  rwa [configurationTranslation_add, neg_add_cancel, configurationTranslation_zero,
    add_neg_cancel_right] at this

/-- The first good event moves with the environment: `ω ∈ G_1(x, K)` implies
`τ_z ω ∈ G_1(x + z, K)`. A path of the translated cluster is the image of a path of the cluster,
with the same sites of `E_R` up to the translation. -/
theorem eventG1_translation (z : Vertex 2) {x : Vertex 2} (hω : ω ∈ eventG1 Cf R c₁ x K) :
    configurationTranslation z ω ∈ eventG1 Cf R c₁ (x + z) K := by
  obtain ⟨h, hG⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  set φ := openComponentTranslationIso z (uniqueInfiniteComponent h)
  intro n γ' hγ' h0 hK
  obtain ⟨γ, rfl⟩ : ∃ γ : Fin (n + 1) → uniqueInfiniteComponent h, γ' = fun i => φ (γ i) :=
    ⟨fun i => φ.symm (γ' i), funext fun i => (φ.apply_symm_apply _).symm⟩
  have hval : ∀ i, (φ (γ i)).val = (γ i).val + z := fun i => openComponentTranslationIso_val z _ _
  have hcount : goodCount (configurationTranslation z ω) Cf R (fun i => φ (γ i)) =
      goodCount ω Cf R γ := by
    unfold goodCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hval, translation_mem_eventE_iff]
  have hγ : IsPathOf _ γ :=
    ⟨Function.Injective.of_comp (f := φ) hγ'.1, fun i => φ.map_adj_iff.mp (hγ'.2 i)⟩
  have h0' : (γ 0).val = x := by
    rw [hval] at h0
    exact add_right_cancel h0
  rw [hval, add_sub_add_right_eq_sub] at hK
  rw [hval, add_sub_add_right_eq_sub, hcount]
  exact hG n γ hγ h0' hK

/-- The printed first good event (changed by [C31]) moves with the
environment. -/
theorem eventG1Exists_translation (z : Vertex 2) {x : Vertex 2}
    (hω : ω ∈ eventG1Exists Cf R c₁ x K) :
    configurationTranslation z ω ∈ eventG1Exists Cf R c₁ (x + z) K := by
  obtain ⟨h, n, γ, hγ, h0, hK, hc⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  set φ := openComponentTranslationIso z (uniqueInfiniteComponent h)
  have hval : ∀ i, (φ (γ i)).val = (γ i).val + z := fun i => openComponentTranslationIso_val z _ _
  have hcount : goodCount (configurationTranslation z ω) Cf R (fun i => φ (γ i)) =
      goodCount ω Cf R γ := by
    unfold goodCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hval, translation_mem_eventE_iff]
  refine ⟨n, fun i => φ (γ i), ⟨φ.injective.comp hγ.1, fun i => φ.map_adj_iff.mpr (hγ.2 i)⟩,
    by rw [hval, h0], ?_, ?_⟩
  · rwa [hval, add_sub_add_right_eq_sub]
  · rwa [hval, add_sub_add_right_eq_sub, hcount]

/-- The second good event moves with the environment. -/
theorem eventG2_translation (z : Vertex 2) {x : Vertex 2} (hω : ω ∈ eventG2 x K) :
    configurationTranslation z ω ∈ eventG2 (x + z) K := by
  obtain ⟨h, hG⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  intro ℓ hℓ R' hR' a b ha hb
  have := hG _ (isCorrectedPlane_comp_translation z hℓ) R' hR'
    ((openComponentTranslationIso z _).symm a) ((openComponentTranslationIso z _).symm b)
    (by rwa [openComponentTranslationIso_symm_val, sub_mem_cubeAt_iff])
    (by rwa [openComponentTranslationIso_symm_val, sub_mem_cubeAt_iff])
  simpa only [RelIso.apply_symm_apply] using this

/-- The third good event moves with the environment:
`ω ∈ G_3(x, C_χ)` implies `τ_z ω ∈ G_3(x + z, C_χ)`. -/
theorem eventG3_translation (z : Vertex 2) {x : Vertex 2} (hω : ω ∈ eventG3 x Cχ) :
    configurationTranslation z ω ∈ eventG3 (x + z) Cχ := by
  obtain ⟨h, hx, y, hadj, hG⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  have hxz : x + z ∈ (openComponentTranslation z ω (uniqueInfiniteComponent h)).supp :=
    (add_mem_openComponentTranslation_supp z _ x).mpr hx
  have e0 : (⟨x + z, hxz⟩ : openComponentTranslation z ω (uniqueInfiniteComponent h)) =
      openComponentTranslationIso z (uniqueInfiniteComponent h) ⟨x, hx⟩ := rfl
  refine ⟨hxz, openComponentTranslationIso z _ y, ?_, fun ℓ hℓ => ?_⟩
  · rw [e0]
    exact (openComponentTranslationIso z _).map_adj_iff.mpr hadj
  · rw [e0]
    exact hG _ (isCorrectedPlane_comp_translation z hℓ)

/-- The printed third good event (changed by [C32]) moves with the
environment. -/
theorem eventG3Edge_translation (z : Vertex 2) {x : Vertex 2} (hω : ω ∈ eventG3Edge x Cχ) :
    configurationTranslation z ω ∈ eventG3Edge (x + z) Cχ := by
  obtain ⟨h, hx, hx1, hadj, hG⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  set C := uniqueInfiniteComponent h
  set φ := openComponentTranslationIso z C
  have hxz : x + z ∈ (openComponentTranslation z ω C).supp :=
    (add_mem_openComponentTranslation_supp z C x).mpr hx
  have hxz1 : x + z + e1 ∈ (openComponentTranslation z ω C).supp := by
    rw [add_right_comm]
    exact (add_mem_openComponentTranslation_supp z C _).mpr hx1
  have e0 : (⟨x + z, hxz⟩ : openComponentTranslation z ω C) = φ ⟨x, hx⟩ := rfl
  have e1' : (⟨x + z + e1, hxz1⟩ : openComponentTranslation z ω C) = φ ⟨x + e1, hx1⟩ :=
    Subtype.ext (show x + z + e1 = x + e1 + z from add_right_comm _ _ _)
  refine ⟨hxz, hxz1, ?_, fun ℓ hℓ => ?_⟩
  · rw [e0, e1']
    exact φ.map_adj_iff.mpr hadj
  · rw [e0, e1']
    exact hG _ (isCorrectedPlane_comp_translation z hℓ)

/-- The good event moves with the environment. -/
theorem eventG_translation (z : Vertex 2) {x : Vertex 2} (hω : ω ∈ eventG Cf R c₁ x Cχ K) :
    configurationTranslation z ω ∈ eventG Cf R c₁ (x + z) Cχ K :=
  ⟨⟨eventG1_translation z hω.1.1, eventG2_translation z hω.1.2⟩, eventG3_translation z hω.2⟩

/-- **Step `GoodEventTranslationStep`** (stationarity, L2381): `ω ∈ G(x, C_χ, K)` if and only if
`τ_{-x} ω ∈ G(0, C_χ, K)`. -/
theorem goodEventTranslationStep : GoodEventTranslationStep := by
  intro Cf R c₁ Cχ K x ω
  constructor
  · intro hω
    have := eventG_translation (-x) hω
    rwa [add_neg_cancel] at this
  · intro hω
    have := eventG_translation x hω
    rwa [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero,
      zero_add] at this

/-! ### The first good event -/

/-- An infinite set of sites contains a site of `ℓ¹` norm at least `K`. -/
theorem exists_mem_le_l1 {S : Set (Vertex 2)} (hS : S.Infinite) (K : ℝ) :
    ∃ y ∈ S, K ≤ l1 y := by
  set N : ℤ := ((⌈K⌉₊ : ℕ) : ℤ)
  obtain ⟨y, hy, hyN⟩ := hS.exists_notMem_finset
    (Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-N) N)
  refine ⟨y, hy, ?_⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hyN
  obtain ⟨i, hi⟩ := hyN
  have hNi : N ≤ |y i| := by
    by_contra hlt
    exact hi (abs_le.mp (not_le.mp hlt).le)
  calc K ≤ (N : ℝ) := by simpa [N] using Nat.le_ceil K
    _ ≤ |(y i : ℝ)| := by exact_mod_cast hNi
    _ ≤ l1 y := Finset.single_le_sum (f := fun j => |(y j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)

/-- **Step `FirstGoodEventStep`** (eq. `PG1goesto1`, [C31]): if the origin lies in the infinite
cluster and `G_1(0, K)` fails, the event of Proposition 5.24 holds: some path of the cluster from
the origin with `|γ(end)| ≥ K` has fewer than `c₁ |γ(end)|` of its sites in `E_R`. -/
theorem firstGoodEventStep : FirstGoodEventStep := by
  rintro Cf R c₁ K ω ⟨⟨h, -⟩, hG1⟩
  by_contra hbad
  refine hG1 ⟨h, fun n γ hγ h0 hK => ?_⟩
  by_contra hlt
  exact hbad ⟨h, n, γ, hγ, h0, by simpa using hK, by simpa using (not_le.mp hlt).le⟩

/-- `FirstGoodEventStep` for the printed first good event (changed by [C31]):
the infinite cluster is connected and infinite, so a path of the cluster from the origin reaches
`|γ(end)| ≥ K`. -/
theorem firstGoodEventStep_printed (Cf : ℕ) (R c₁ K : ℝ) :
    {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp} \
        eventG1Exists Cf R c₁ 0 K ⊆ badPathEvent Cf R c₁ K := by
  revert Cf R c₁ K
  rintro Cf R c₁ K ω ⟨⟨h, h0⟩, hG1⟩
  set C := uniqueInfiniteComponent h
  obtain ⟨y, hy, hyK⟩ := exists_mem_le_l1 (uniqueInfiniteComponent_infinite h) K
  obtain ⟨p⟩ := (SimpleGraph.ConnectedComponent.connected_toSimpleGraph C).preconnected
    (⟨0, h0⟩ : C) ⟨y, hy⟩
  set W := p.toPath.1
  have hW : W.IsPath := p.toPath.2
  set γ : Fin (W.length + 1) → C := fun i => W.getVert i
  have hγ : IsPathOf C γ := by
    refine ⟨fun i j hij => Fin.ext (hW.getVert_injOn (Nat.lt_succ_iff.mp i.2)
      (Nat.lt_succ_iff.mp j.2) hij), fun i => ?_⟩
    simpa [γ] using W.adj_getVert_succ i.2
  have hγ0 : γ 0 = ⟨0, h0⟩ := W.getVert_zero
  have hγn : γ (Fin.last _) = ⟨y, hy⟩ := W.getVert_length
  refine ⟨h, W.length, γ, hγ, by rw [hγ0], by rwa [hγn], ?_⟩
  by_contra hlt
  refine hG1 ⟨h, W.length, γ, hγ, by rw [hγ0], by rwa [hγn, sub_zero], ?_⟩
  rw [sub_zero]
  exact (not_le.mp hlt).le

/-- Lemma 5.25 from Theorem 2.5, the uniqueness of the infinite cluster, Proposition 3.2 and its
two remaining steps, for `p_c(2) < p < 1`. -/
theorem goodEventLowerBound_of_second_third {p : unitInterval}
    (hQ : Rigidity.External.CorrectorQuantitativeInput)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h32 : Rigidity.Section3.NotLipschitzStmt 2 p) (h2 : SecondGoodEventStep)
    (h3 : ThirdGoodEventStep) : GoodEventLowerBoundStmt p :=
  goodEventLowerBound_of_steps hQ hUq hU hpc hp1 h32 goodEventTranslationStep firstGoodEventStep
    h2 h3

end Rigidity.Proofs.Section5
