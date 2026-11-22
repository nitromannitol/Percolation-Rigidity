import Rigidity.Proofs.Cluster.MeyersPlanarBox
import Rigidity.Proofs.Cluster.PartitionBoxSobolev

/-!
# The Meyers estimate on the crossing clusters of the partition into good cubes

Armstrong and Dario, Proposition 3.8, deterministic part, in every dimension `d ≥ 2`, with the
Sobolev inequality of Proposition 3.4 proved on the clusters of the triples `3□'` of the cubes used
by the Gehring argument. For a cube `□' = cube k y` whose triple `3□'` has partition cubes of scale
less than `k` at its vertices, the cluster `C(3□')` of the integer cube `enlSquare k y`
(`partitionBoxCluster`) lies in the crossing cluster `𝒞_*(V)` of every resolved triadic cube
`V ⊇ 3□'`, is closed under open edges inside `3□'`, contains the vertices of `𝒞_*(V) ∩ □'` (their
local paths stay in `3□'`), and carries the Sobolev inequality `exists_clusterSobolevTwo_box`.

`partition_meyers` is Proposition 3.8 for functions harmonic on `𝒞_*(V) ∩ 3□`, `3□ ⊆ V`. Its
remaining hypotheses are:
* the partition event and the resolution of `V`;
* a Gehring partition into cells `cube (s x) x` with comparable neighbours tiling `3□`, with the
  moment bound `∑_{x ∈ □} (3^{s(x)})^t ≤ K |□|` (the partition `𝓡` above its minimal scale);
* for every triadic `□' = cube k y` containing a cell with `3□' ⊆ 3□`: the partition cubes of the
  vertices of `3□'` have scale less than `k`, and the reach of the partition satisfies
  `∑_{z ∈ 3□'} partitionReach(z)^{2d(d+2)} ≤ C_G |3□'|` (the good event of `𝓡`).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal

variable {d : ℕ} {ω : Configuration d}

/-- If the partition cubes of the vertices of `3□'`, `□' = cube k y`, have scale less than `k`,
the integer cube `3□'` is resolved by the partition into good cubes. -/
theorem partitionBoxResolved_enlSquare (hP : PartitionEvent ω) {k : ℕ} {y : Vertex d}
    (h : ∀ z ∈ enl 1 k y, (partitionCube ω z).scale + 1 ≤ k) :
    PartitionBoxResolved ω (enlSquare k y) := by
  intro z hz x hx
  have hzE : z ∈ enl 1 k y := mem_enlSquare_vertices.1 hz
  have hzP := (partitionCube ω z).vertices_subset_parent (mem_partitionCube hP z)
  have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le (R := ⟨k, idx k z⟩) hzP
    (mem_triadicCube_idx_iff.2 (mem_cube_self k z)) (show (partitionCube ω z).scale + 1 ≤ k
      from h z hzE) hx
  exact mem_enlSquare_vertices.2 (cube_subset_enl_of_mem hzE (mem_triadicCube_idx_iff.1 hsub))

/-- The cluster of an integer cube inside a resolved triadic cube `V` lies in the crossing cluster
of `V`. -/
theorem partitionBoxCluster_subset_crossingClusterVertices (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {V : TriadicCube d}
    (hV : PartitionResolved ω V) (hBV : (↑B.vertices : Set (Vertex d)) ⊆ V.vertices) :
    partitionBoxCluster ω B ⊆ crossingClusterVertices ω V := by
  intro x hx
  have hx' := mem_partitionBoxCluster.1 hx
  have hxV : x ∈ V.vertices := hBV hx'.1
  have hA : partitionAnchor ω x ∈ V.crossingCluster ω :=
    crossingCluster_partitionCube_subset hd hP hxV (hV x hxV)
      (partitionAnchor_mem_crossingCluster hP x)
  have h1 : (openIn ω (V.vertices ∩ ↑B.vertices)).Reachable (partitionAnchor ω x) x :=
    reachable_openIn_mono (show (↑B.vertices : Set (Vertex d)) ⊆ V.vertices ∩ ↑B.vertices from
      fun z hz => ⟨hBV hz, hz⟩) hx'.2.symm
  have h2 := TriadicCube.reachable_crossingCluster_inter hA h1
  have hAB : partitionAnchor ω x ∈ (↑B.vertices : Set (Vertex d)) :=
    hB.partitionCube_subset hx'.1 (partitionAnchor_mem hP x)
  exact mem_crossingClusterVertices.2 (mem_of_reachable_openIn_of_mem
    (show partitionAnchor ω x ∈ V.crossingCluster ω ∩ ↑B.vertices from ⟨hA, hAB⟩) h2).1

/-- A vertex of the crossing cluster of a resolved triadic cube `V` lying in `□' = cube k y`
belongs to the cluster of `3□'`, if the partition cubes of `3□'` have scale less than `k`. -/
theorem mem_partitionBoxCluster_of_mem_cube (hd : 0 < d) (hP : PartitionEvent ω) {k : ℕ}
    {y : Vertex d} {V : TriadicCube d} (hV : PartitionResolved ω V)
    (hres : ∀ z ∈ enl 1 k y, (partitionCube ω z).scale + 1 ≤ k) {x : Vertex d}
    (hx : x ∈ crossingClusterVertices ω V) (hxc : x ∈ cube k y) :
    x ∈ partitionBoxCluster ω (enlSquare k y) := by
  have hxE : x ∈ enl 1 k y := cube_subset_enl 1 k y hxc
  have hxB : x ∈ (enlSquare k y).vertices := mem_enlSquare_vertices.2 hxE
  have hxC := mem_crossingClusterVertices.1 hx
  have hxV : x ∈ V.vertices := V.crossingCluster_subset ω hxC
  have h := reachable_partitionAnchor_of_mem_crossingCluster hd hP hxV (hV x hxV) hxC
  have hs := hres x hxE
  set Q := partitionCube ω x with hQ
  -- the region of the local path lies in `3□'`
  have hreg : Q.parent.vertices ∪ cubeAt x (3 ^ Q.scale - 1) ⊆
      ↑(enlSquare k y).vertices := by
    rintro z (hz | hz)
    · have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le (R := ⟨k, idx k y⟩)
        (Q.vertices_subset_parent (mem_partitionCube hP x)) (mem_triadicCube_idx_iff.2 hxc)
        (show Q.scale + 1 ≤ k from hs) hz
      exact mem_enlSquare_vertices.2 (cube_subset_enl 1 k y (mem_triadicCube_idx_iff.1 hsub))
    · rw [Finset.mem_coe, mem_enlSquare_vertices, enl, mem_box]
      rw [cube, mem_box] at hxc
      intro i
      have h1 := hxc i
      have h2 := hz i
      have h3 := two_mul_halfSide_add_one k
      have h4 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
      have h5 : (3 : ℤ) ^ Q.scale ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have h6 : ((3 ^ Q.scale - 1 : ℕ) : ℤ) ≤ 3 ^ Q.scale := by
        have : (3 ^ Q.scale - 1 : ℕ) ≤ 3 ^ Q.scale := Nat.sub_le _ _
        exact_mod_cast this
      calc |z i - center k y i| ≤ |z i - x i| + |x i - center k y i| := abs_sub_le _ _ _
        _ ≤ halfSide (k + 1) := by omega
  refine mem_partitionBoxCluster.2 ⟨hxB, reachable_openIn_mono ?_ h⟩
  rintro z ⟨-, hz⟩
  exact hreg hz

/-- **The Meyers estimate on the crossing clusters of the partition into good cubes**
(Armstrong–Dario, Proposition 3.8, deterministic part, in every dimension `d ≥ 2`, with the
Sobolev inequality of Proposition 3.4 on the clusters of the triples `3□'` proved). For constants
`C_G, K ≥ 0` there are `ε > 0`, `t > 0` and `C < ∞` with the following property. On the partition
event, let `V` be a resolved triadic cube containing `3□ = enl 1 n x₀`, `u` harmonic at the vertices
of `𝒞_*(V) ∩ 3□` whose open neighbours lie in `𝒞_*(V)`, the cells `cube (s x) x` of a partition of
`ℤᵈ` have comparable neighbours and tile `3□`, with `∑_{x ∈ □} (3^{s(x)})^t ≤ K |□|`, and let every
triadic cube `□' = cube k y` containing a cell with `3□' ⊆ 3□` have partition cubes of scale less
than `k` at the vertices of `3□'` and `∑_{z ∈ 3□'} partitionReach(z)^{2d(d+2)} ≤ C_G |3□'|`. Then,
with `E = |∇u 1_{𝐚≠0}|²` on `𝒞_*(V)` (zero outside), `avg_□ E^{1+ε/2} ≤ C (avg_{3□} E)^{1+ε/2}`. -/
theorem partition_meyers (hd : 2 ≤ d) {CG K : ℝ} (hCG : 0 ≤ CG) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration d) (_ : PartitionEvent ω) (V : TriadicCube d)
        (_ : PartitionResolved ω V) (n : ℕ) (x₀ : Vertex d) (u : Vertex d → ℝ)
        (s : Vertex d → ℕ),
        (↑(enl 1 n x₀) : Set (Vertex d)) ⊆ V.vertices →
        (∀ x ∈ crossingClusterVertices ω V, x ∈ enl 1 n x₀ →
          (∀ y, (openGraph ω).Adj x y → y ∈ crossingClusterVertices ω V) →
            openLaplacian ω u x = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (partitionCube ω z).scale + 1 ≤ k) ∧
            ∑ z ∈ enl 1 k y, partitionReach ω z ^ (2 * d * (d + 2)) ≤
              ENNReal.ofReal CG * 3 ^ ((k + 1) * d)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (crossingClusterVertices ω V) u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω (crossingClusterVertices ω V) u) ^ (1 + ε / 2) := by
  have hd0 : 0 < d := by omega
  obtain ⟨K₀, hK₀, hSobK⟩ := exists_clusterSobolevTwo_box hd
  obtain ⟨ε, hε, t, ht, C, hC, hM⟩ := meyers_cluster_of_local (d := d) (by omega) hK₀ hCG hK
  refine ⟨ε, hε, t, ht, C, hC, ?_⟩
  intro ω hP V hV n x₀ u s hVsub hu hcell hnb hΩ hcubes hmom
  refine hM ω n x₀ (crossingClusterVertices ω V) u s hu hcell hnb hΩ
    (fun k y hk hsub => ?_) hmom
  obtain ⟨hres, hreach⟩ := hcubes k y hk hsub
  have hBr := partitionBoxResolved_enlSquare hP hres
  set B := enlSquare k y with hBdef
  have hBpos : 0 < B.size := by
    change 0 < 3 ^ (k + 1)
    positivity
  set U' := partitionBoxCluster ω B with hU'def
  set P := partitionBoxCoarseData hd0 hP B hBr with hPdef
  set size : Vertex d → ℝ := fun z => (3 : ℝ) ^ P.reachScale z with hsizedef
  have hU'E : ∀ z ∈ U', z ∈ enl 1 k y := fun z hz =>
    mem_enlSquare_vertices.1 (Finset.mem_filter.1 hz).1
  have hBV : (↑B.vertices : Set (Vertex d)) ⊆ V.vertices := fun z hz =>
    hVsub (Finset.mem_coe.2 (hsub (mem_enlSquare_vertices.1 (Finset.mem_coe.1 hz))))
  -- the moment bound
  have hN : (2 * (d : ℝ) * ((d : ℝ) + 2)) = ((2 * d * (d + 2) : ℕ) : ℝ) := by push_cast; ring
  have hmomR : ∑ z ∈ U', size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2)) ≤ CG * (3 : ℝ) ^ ((k + 1) * d) := by
    have hterm : ∀ z ∈ U', ENNReal.ofReal (size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2))) ≤
        partitionReach ω z ^ (2 * d * (d + 2)) := by
      intro z hz
      rw [hN, Real.rpow_natCast, hsizedef, ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      exact pow_le_pow_left₀ zero_le (three_pow_reachScale_le_partitionReach_box hd0 hP hBr hz) _
    have hsum : ENNReal.ofReal (∑ z ∈ U', size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2))) ≤
        ENNReal.ofReal (CG * (3 : ℝ) ^ ((k + 1) * d)) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun z _ => Real.rpow_nonneg (by positivity) _]
      calc ∑ z ∈ U', ENNReal.ofReal (size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2)))
          ≤ ∑ z ∈ U', partitionReach ω z ^ (2 * d * (d + 2)) := Finset.sum_le_sum hterm
        _ ≤ ∑ z ∈ enl 1 k y, partitionReach ω z ^ (2 * d * (d + 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hU'E fun _ _ _ => zero_le
        _ ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * d) := hreach
        _ = ENNReal.ofReal (CG * (3 : ℝ) ^ ((k + 1) * d)) := by
            rw [ENNReal.ofReal_mul hCG, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsum
  refine ⟨U', size, fun z => by positivity, hU'E, ?_, ?_, ?_, ?_, ?_⟩
  · exact partitionBoxCluster_subset_crossingClusterVertices hd0 hP hBr hV hBV
  · intro z hz w hadj hw
    exact mem_partitionBoxCluster_of_adj hd0 hP hBr hz hadj (mem_enlSquare_vertices.2 hw)
  · exact fun x hx hxc => mem_partitionBoxCluster_of_mem_cube hd0 hP hV hres hx hxc
  · exact hSobK ω hP B hBpos hBr
  · exact hmomR

end Rigidity.Proofs.Cluster
