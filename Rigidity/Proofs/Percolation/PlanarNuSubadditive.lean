import Rigidity.Proofs.Percolation.PlanarMuSubadditive

/-!
# Subadditivity of `ν` on the planar cluster

Let `U` be a triadic cube of scale `m`, `n ≤ m`, and `v` the maximizer of `ν(U, p)`.
Testing the definition of `ν(V, p)`, for every resolved subcube `V` of scale `n`, with the
restriction of `v`, the energies of the restrictions add up to at most the energy of `v`, and the
flux pairings add up to the flux pairing of `v` except for the open edges of the cluster of `U`
which do not lie in the cluster of a resolved subcube:

`|U| ν(U, p) ≤ ∑_{x ∈ U} 1{V(x) resolved} ν(V(x), p) + F_p^{exc}(v)`,

where `F_p^{exc}` is the flux pairing over these exceptional open edges (Armstrong and Dario,
Lemma 4.8, (4.18)).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The flux pairing as a sum over the cluster as a finite set. -/
theorem fluxPairing_eq_sum {U : TriadicCube 2} (p : Fin 2 → ℝ) (u : ClusterFun ω U) :
    fluxPairing ω U p u = (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
      (if (openGraph ω).Adj x y then (∑ i, p i * ((y i : ℝ) - x i)) *
        (clusterExtend ω U u y - clusterExtend ω U u x) else 0) := by
  rw [fluxPairing_apply]
  congr 1
  rw [← Finset.sum_coe_sort (clusterVertices ω U)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_coe_sort (clusterVertices ω U)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [clusterExtend_apply_of_mem u x.2, clusterExtend_apply_of_mem u y.2]

/-- Sums over the clusters of resolved subcubes, indexed by the first vertex. -/
theorem sum_subcubes_cluster_eq {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (T : Finset (TriadicCube 2)) (hT : T ⊆ subcubesAt U n)
    (H : TriadicCube 2 → Vertex 2 → ℝ) :
    ∑ V ∈ T, ∑ x ∈ clusterVertices ω V, H V x =
      ∑ x ∈ clusterVertices ω U, (if scaleCube n x ∈ T ∧
        x ∈ clusterVertices ω (scaleCube n x) then H (scaleCube n x) x else 0) := by
  have hsubU : ∀ V ∈ T, clusterVertices ω V ⊆ clusterVertices ω U := fun V hV =>
    clusterVertices_subset (subset_of_mem_subcubesAt hn (hT hV))
  have hVx : ∀ V ∈ T, ∀ x ∈ clusterVertices ω V, scaleCube n x = V := by
    intro V hV x hx
    obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.1 (hT hV)
    exact scaleCube_eq_of_mem (mem_clusterVertices.1 hx).1
  calc ∑ V ∈ T, ∑ x ∈ clusterVertices ω V, H V x
      = ∑ V ∈ T, ∑ x ∈ clusterVertices ω V, H (scaleCube n x) x :=
        Finset.sum_congr rfl fun V hV => Finset.sum_congr rfl fun x hx => by
          rw [hVx V hV x hx]
    _ = ∑ x ∈ T.biUnion (fun V => clusterVertices ω V), H (scaleCube n x) x :=
        (Finset.sum_biUnion (pairwiseDisjoint_clusterVertices U n T hT)).symm
    _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · rintro ⟨V, hV, hx⟩
          rw [hVx V hV x hx]
          exact ⟨hsubU V hV hx, hV, hx⟩
        · rintro ⟨_, hT', hx⟩
          exact ⟨_, hT', hx⟩

/-- The flux term of an ordered pair of open neighbours. -/
noncomputable def fluxTerm (ω : Configuration 2) (U : TriadicCube 2) (p : Fin 2 → ℝ)
    (v : ClusterFun ω U) (x y : Vertex 2) : ℝ :=
  if (openGraph ω).Adj x y then
    (∑ i, p i * ((y i : ℝ) - x i)) * (clusterExtend ω U v y - clusterExtend ω U v x)
  else 0

theorem fluxPairing_eq_sum_fluxTerm {U : TriadicCube 2} (p : Fin 2 → ℝ) (v : ClusterFun ω U) :
    fluxPairing ω U p v = (1 / 2 : ℝ) *
      ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U, fluxTerm ω U p v x y :=
  fluxPairing_eq_sum p v

/-- The flux pairing of a restriction. -/
theorem fluxPairing_restrictExt (V : TriadicCube 2) {U : TriadicCube 2} (p : Fin 2 → ℝ)
    (v : ClusterFun ω U) :
    fluxPairing ω V p (clusterRestrictExt V v) = (1 / 2 : ℝ) *
      ∑ x ∈ clusterVertices ω V, ∑ y ∈ clusterVertices ω V, fluxTerm ω U p v x y := by
  have hext : ∀ y ∈ clusterVertices ω V,
      clusterExtend ω V (clusterRestrictExt V v) y = clusterExtend ω U v y := by
    intro y hy
    rw [clusterExtend_apply_of_mem _ hy]
    rfl
  rw [fluxPairing_eq_sum]
  refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun x hx =>
    Finset.sum_congr rfl fun y hy => ?_)
  simp only [fluxTerm]
  rw [hext y hy, hext x hx]

/-- The exceptional pairs: those not lying in the cluster of a resolved subcube. -/
def IsSubcubePair (ω : Configuration 2) (n : ℕ) (x y : Vertex 2) : Prop :=
  PlanarResolved ω (scaleCube n x) ∧ x ∈ clusterVertices ω (scaleCube n x) ∧
    y ∈ clusterVertices ω (scaleCube n x)

/-- The flux pairings of the restrictions to resolved subcubes. -/
theorem sum_fluxPairing_restrictExt {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (p : Fin 2 → ℝ) (v : ClusterFun ω U) :
    ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
        fluxPairing ω V p (clusterRestrictExt V v) =
      (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
        (if IsSubcubePair ω n x y then fluxTerm ω U p v x y else 0) := by
  set T := (subcubesAt U n).filter (fun V => PlanarResolved ω V)
  have hTS : T ⊆ subcubesAt U n := Finset.filter_subset _ _
  have hsubU : ∀ V ∈ T, clusterVertices ω V ⊆ clusterVertices ω U := fun V hV =>
    clusterVertices_subset (subset_of_mem_subcubesAt hn (hTS hV))
  have hSx : ∀ x ∈ clusterVertices ω U, scaleCube n x ∈ subcubesAt U n := fun x hx =>
    Finset.mem_image_of_mem _
      ((U.mem_toIntegerCube_vertices x).2 (mem_clusterVertices.1 hx).1)
  rw [Finset.sum_congr rfl fun V _ => fluxPairing_restrictExt V p v, ← Finset.mul_sum]
  refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
  rw [sum_subcubes_cluster_eq hn T hTS
    (fun V x => ∑ y ∈ clusterVertices ω V, fluxTerm ω U p v x y)]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hT : scaleCube n x ∈ T ↔ PlanarResolved ω (scaleCube n x) := by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hSx x hx, h⟩⟩
  by_cases hc : PlanarResolved ω (scaleCube n x) ∧ x ∈ clusterVertices ω (scaleCube n x)
  · have hc' : scaleCube n x ∈ T ∧ x ∈ clusterVertices ω (scaleCube n x) := ⟨hT.2 hc.1, hc.2⟩
    rw [if_pos hc', ← Finset.sum_filter]
    have hsub := hsubU _ hc'.1
    congr 1
    ext y
    simp only [Finset.mem_filter, IsSubcubePair]
    exact ⟨fun h => ⟨hsub h, hc.1, hc.2, h⟩, fun h => h.2.2.2⟩
  · have hc' : ¬ (scaleCube n x ∈ T ∧ x ∈ clusterVertices ω (scaleCube n x)) :=
      fun h => hc ⟨hT.1 h.1, h.2⟩
    rw [if_neg hc']
    symm
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    exact fun h => hc ⟨h.1, h.2.1⟩

/-- **Subadditivity of `ν`** (planar form of Armstrong and Dario, Lemma 4.8, (4.18)). -/
theorem planarNu_le_sum_subcubes (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    {n : ℕ} (hn : n ≤ U.scale) (p : Fin 2 → ℝ) :
    ∃ v ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w v = fluxPairing ω U p w) ∧
      planarNu ω U p * U.volume ≤
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) p else 0) +
        (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
          (if IsSubcubePair ω n x y then 0 else fluxTerm ω U p v x y) := by
  obtain ⟨v, hv, hvar, hν⟩ := exists_planarNu_maximizer (ω := ω) (U := U) p
  refine ⟨v, hv, hvar, ?_⟩
  set T := (subcubesAt U n).filter (fun V => PlanarResolved ω V)
  have hTS : T ⊆ subcubesAt U n := Finset.filter_subset _ _
  have hL : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) p else 0) =
      ∑ V ∈ T, V.volume * planarNu ω V p := by
    rw [sum_scaleCube_eq hn (fun V _ => if PlanarResolved ω V then planarNu ω V p else 0),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun V _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← volume_eq_card]
    split_ifs <;> simp
  have hV : ∀ V ∈ T, fluxPairing ω V p (clusterRestrictExt V v) -
      clusterForm ω V (clusterRestrictExt V v) (clusterRestrictExt V v) / 2 ≤
      V.volume * planarNu ω V p := by
    intro V hVT
    obtain ⟨hVS, hVres⟩ := Finset.mem_filter.1 hVT
    have hVU := subset_of_mem_subcubesAt hn hVS
    have hmem : clusterRestrictExt V v ∈ clusterHarmonic ω V := by
      rw [clusterRestrictExt_eq hVU]
      exact clusterRestrict_mem_clusterHarmonic hP hVres hVU hv
    have h := le_planarNu p hmem
    rw [div_le_iff₀ V.volume_pos] at h
    linarith
  have hFU : fluxPairing ω U p v =
      ∑ V ∈ T, fluxPairing ω V p (clusterRestrictExt V v) +
      (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
        (if IsSubcubePair ω n x y then 0 else fluxTerm ω U p v x y) := by
    rw [sum_fluxPairing_restrictExt hn p v, fluxPairing_eq_sum_fluxTerm, ← mul_add,
      ← Finset.sum_add_distrib]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun x _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have hBU := sum_clusterForm_restrict_le hn T hTS v
  have hνU : planarNu ω U p * U.volume = fluxPairing ω U p v - clusterForm ω U v v / 2 := by
    rw [hν, div_mul_cancel₀ _ U.volume_pos.ne']
  rw [hL, hνU, hFU]
  have hsumV := Finset.sum_le_sum hV
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hsumV
  linarith

end Rigidity.Percolation
