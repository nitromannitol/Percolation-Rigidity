import Rigidity.Proofs.Cluster.MeyersCluster
import Rigidity.Proofs.Cluster.PlanarBoxSobolev
import Rigidity.Proofs.Cluster.ReverseHolderPlanar

/-!
# The Meyers estimate on planar clusters

Armstrong and Dario, Proposition 3.8, deterministic part, in dimension two, with the Sobolev
inequality of Proposition 3.4 proved on the clusters of the triples `3□'`.

`meyers_cluster_of_local` is `meyers_cluster` with a weight `size` chosen for each cube `□'`. In
the proof of Proposition 3.8 the reverse Hölder inequality (Lemma 3.6) is used on every triadic cube
`□'` containing a cell of the Gehring partition with `3□' ⊆ 3□`, and its proof needs the Sobolev
inequality on a cluster of the triple `3□'`, an integer square of side `3^{k+1}` which is not
triadic in general. Here this cluster is the cluster `C(3□')` of the integer square `enlSquare k y`
(`planarBoxCluster`): if the planar partition cubes of the vertices of `3□'` have scale at most
`k`, it lies in the cluster of every triadic cube `V ⊇ 3□'`, is closed under open edges inside
`3□'`, contains the vertices of `𝒞(V) ∩ □'` (they are at distance `3^k` from the complement of
`3□'`), and carries the Sobolev inequality `exists_planarBox_sum_sq_le`.

`planar_meyers` is then Proposition 3.8 for functions harmonic on the cluster `𝒞(V)` of a triadic
cube `V ⊇ 3□`. Its hypotheses are:
* the planar partition event (it holds almost surely, `ae_planarPartitionEvent`);
* a Gehring partition into cells `cube (s x) x` with comparable neighbours tiling `3□`, and the
  moment bound `∑_{x ∈ □} (3^{s(x)})^t ≤ K |□|` of its cell sizes (the partition `𝓡` of Armstrong
  and Dario above its minimal scale);
* for every triadic `□' = cube k y` containing a cell with `3□' ⊆ 3□`: the planar partition cubes
  of the vertices of `3□'` have scale at most `k`, and the reach of the planar partition satisfies
  `∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G |3□'|` (the good event of `𝓡`, which replaces the
  condition `3^m ≥ 𝓜_{2sd}(𝒫) + C` of Lemma 3.6 at `□'`);
* `u` harmonic at the vertices of `𝒞(V) ∩ 3□` whose open neighbours lie in `𝒞(V)` (this holds
  for the functions of `A_*(V)` when the lattice neighbours of `3□` lie in `V`).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {d : ℕ}

/-- **The reverse Hölder inequality for the energy density, for functions harmonic near the
cube** (Armstrong–Dario, Lemma 3.6 with `s = d + 2`, in the form used by Proposition 3.8). As
`reverse_holder_clusterEnergy`, with `u` harmonic only at the vertices of `U₀ ∩ 3□'`: let
`U' ⊆ U₀ ∩ 3□'`, `□' = cube k y`, be closed under open edges inside `3□'` and contain `U₀ ∩ □'`,
with the Sobolev inequality and the moment bound `∑_{U'} size^{2d(d+2)} ≤ C_G |3□'|`. Then
`avg_{□'} E ≤ 8d C_S C_G^{2/((d+2) 2_*)} 3^{d+2} (avg_{3□'} E^{d/(d+1)})^{(d+1)/d}`. -/
theorem reverse_holder_clusterEnergy_local (ω : Configuration d) (hd : 0 < d)
    (U₀ : Finset (Vertex d)) (u : Vertex d → ℝ) (k : ℕ) (y : Vertex d)
    (hu : ∀ x ∈ U₀, x ∈ enl 1 k y → (∀ w, (openGraph ω).Adj x w → w ∈ U₀) →
      openLaplacian ω u x = 0) (U' : Finset (Vertex d)) (hU'enl : U' ⊆ enl 1 k y) (hU'U₀ : U' ⊆ U₀)
    (hclosed : ∀ z ∈ U', ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k y → w ∈ U')
    (hcap : ∀ x ∈ U₀, x ∈ cube k y → x ∈ U') (size : Vertex d → ℝ) (hsize : ∀ x, 0 ≤ size x)
    {CS CG : ℝ} (hCS : 0 ≤ CS) (hCG : 0 ≤ CG) (hSob : ClusterSobolevTwo ω U' size CS)
    (hgood : ∑ x ∈ U', size x ^ (2 * (d : ℝ) * (d + 2)) ≤ CG * (3 : ℝ) ^ ((k + 1) * d)) :
    avg (cube k y) (clusterEnergy ω U₀ u) ≤
      8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
        avg (enl 1 k y) (fun x => clusterEnergy ω U₀ u x ^ ((d : ℝ) / (d + 1))) ^
          (((d : ℝ) + 1) / d) := by
  obtain ⟨hst, he1, he2⟩ := reverse_holder_exponents (d := d) hd
  set V := (cube k y).filter (· ∈ U₀) with hV
  have hVU' : V ⊆ U' := fun x hx => hcap x (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx).1
  have hVcube : V ⊆ cube k y := Finset.filter_subset _ _
  have hu' : ∀ x ∈ U', (∀ w, (openGraph ω).Adj x w → w ∈ U') → openLaplacian ω u x = 0 :=
    fun x hx hall => hu x (hU'U₀ hx) (hU'enl hx) fun w hw => hU'U₀ (hall w hw)
  have hrh := reverse_holder_triadic ω hd k y U' V hVU' hVcube hclosed size hsize hCS hCG hst
    hSob hgood u hu'
  rw [he1, he2] at hrh
  have hnbr : ∀ x ∈ V, ∀ w, (openGraph ω).Adj x w → w ∈ U₀ → w ∈ U' := by
    intro x hx w hadj _
    refine hclosed x (hVU' hx) w hadj ?_
    have hxc := hVcube hx
    rw [cube, mem_box] at hxc
    rw [enl, mem_box]
    intro i
    have h1 := abs_sub_le_one_of_openGraph_adj hadj i
    have h2 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
    have h3 := halfSide_nonneg k
    have h4 := abs_sub_le (w i) (x i) (center k y i)
    rw [abs_sub_comm (w i) (x i)] at h4
    linarith [hxc i]
  have hL : ∑ x ∈ cube k y, clusterEnergy ω U₀ u x = ∑ x ∈ V, clusterGradSq ω U' u x := by
    rw [hV, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    unfold clusterEnergy
    split_ifs with h
    · exact (clusterGradSq_eq_of_subset ω hU'U₀ u
        (hnbr x (Finset.mem_filter.mpr ⟨hx, h⟩))).symm
    · rfl
  set θ : ℝ := (d : ℝ) / (d + 1) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hR : ∑ x ∈ U', clusterGradSq ω U' u x ^ θ ≤
      ∑ x ∈ enl 1 k y, clusterEnergy ω U₀ u x ^ θ := by
    calc ∑ x ∈ U', clusterGradSq ω U' u x ^ θ ≤ ∑ x ∈ U', clusterEnergy ω U₀ u x ^ θ := by
          refine Finset.sum_le_sum fun x hx => ?_
          have h1 : clusterEnergy ω U₀ u x = clusterGradSq ω U₀ u x := by
            unfold clusterEnergy
            rw [if_pos (hU'U₀ hx)]
          rw [h1]
          exact Real.rpow_le_rpow (clusterGradSq_nonneg ω U' u x)
            (clusterGradSq_le_of_subset ω hU'U₀ u x) hθ0
      _ ≤ ∑ x ∈ enl 1 k y, clusterEnergy ω U₀ u x ^ θ :=
          Finset.sum_le_sum_of_subset_of_nonneg hU'enl fun x _ _ =>
            Real.rpow_nonneg (clusterEnergy_nonneg ω U₀ u x) _
  have hcube : ((cube k y).card : ℝ) = (3 : ℝ) ^ (k * d) := by rw [card_cube, pow_mul]
  have henl : ((enl 1 k y).card : ℝ) = (3 : ℝ) ^ ((k + 1) * d) := by rw [card_enl, pow_mul]
  have hexp : (0 : ℝ) ≤ ((d : ℝ) + 1) / d := by positivity
  have hC : 0 ≤ 8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCS) (Real.rpow_nonneg hCG _))
      (by positivity)
  calc avg (cube k y) (clusterEnergy ω U₀ u)
      = (1 / (3 : ℝ) ^ (k * d)) * ∑ x ∈ V, clusterGradSq ω U' u x := by
        rw [avg, hL, hcube]
        ring
    _ ≤ 8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
          ((1 / (3 : ℝ) ^ ((k + 1) * d)) * ∑ x ∈ U', clusterGradSq ω U' u x ^ θ) ^
            (((d : ℝ) + 1) / d) := hrh
    _ ≤ 8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
          avg (enl 1 k y) (fun x => clusterEnergy ω U₀ u x ^ θ) ^ (((d : ℝ) + 1) / d) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ ?_ hexp) hC
        · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ =>
            Real.rpow_nonneg (clusterGradSq_nonneg ω U' u x) _)
        · rw [avg, henl, one_div_mul_eq_div]
          exact div_le_div_of_nonneg_right hR (by positivity)

/-- **The Meyers estimate on a cluster with a weight for each cube** (Armstrong–Dario,
Proposition 3.8, deterministic part, with the Sobolev inequality of Proposition 3.4 as
hypothesis). As `meyers_cluster`, with `u` harmonic only at the vertices of `U₀ ∩ 3□`, and with
the weight `size` of the Sobolev inequality and of the moment bound chosen for each cube `□'`. -/
theorem meyers_cluster_of_local (hd : 1 ≤ d) {CS CG K : ℝ} (hCS : 0 ≤ CS) (hCG : 0 ≤ CG)
    (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration d) (n : ℕ) (x₀ : Vertex d) (U₀ : Finset (Vertex d))
        (u : Vertex d → ℝ) (s : Vertex d → ℕ),
        (∀ x ∈ U₀, x ∈ enl 1 n x₀ → (∀ y, (openGraph ω).Adj x y → y ∈ U₀) →
          openLaplacian ω u x = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          ∃ (U' : Finset (Vertex d)) (size : Vertex d → ℝ), (∀ x, 0 ≤ size x) ∧
            U' ⊆ enl 1 k y ∧ U' ⊆ U₀ ∧
            (∀ z ∈ U', ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k y → w ∈ U') ∧
            (∀ x ∈ U₀, x ∈ cube k y → x ∈ U') ∧ ClusterSobolevTwo ω U' size CS ∧
            ∑ x ∈ U', size x ^ (2 * (d : ℝ) * (d + 2)) ≤ CG * (3 : ℝ) ^ ((k + 1) * d)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2) := by
  set A₀ : ℝ := max 1 (8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) *
    (3 : ℝ) ^ (d + 2)) with hA₀
  obtain ⟨ε, hε, t, ht, C, hC, hM⟩ := meyers_triadic (d := d) hd (le_max_left 1 _) hK (A₀ := A₀)
  refine ⟨ε, hε, t, ht, C, hC, ?_⟩
  intro ω n x₀ U₀ u s hu hcell hnb hΩ hcubes hmom
  refine hM n x₀ (clusterEnergy ω U₀ u) s (clusterEnergy_nonneg ω U₀ u) hcell hnb hΩ ?_ hmom
  intro k y hk hsub
  obtain ⟨U', size, hsize, h1, h2, h3, h4, h5, h6⟩ := hcubes k y hk hsub
  have hrh := reverse_holder_clusterEnergy_local ω (by omega) U₀ u k y
    (fun x hx hxe hall => hu x hx (hsub hxe) hall) U' h1 h2 h3 h4 size hsize hCS hCG h5 h6
  refine hrh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ?_ _))
  exact div_nonneg (Finset.sum_nonneg fun x _ =>
    Real.rpow_nonneg (clusterEnergy_nonneg ω U₀ u x) _) (Nat.cast_nonneg _)

/-- The integer cube `3□'` of side `3^{k+1}` around the triadic cube `□' = cube k y`. -/
def enlSquare (k : ℕ) (y : Vertex d) : IntegerCube d :=
  ⟨fun i => center k y i - halfSide (k + 1), 3 ^ (k + 1)⟩

theorem enlSquare_size (k : ℕ) (y : Vertex d) : (enlSquare k y).size = 3 ^ (k + 1) :=
  rfl

theorem mem_enlSquare_vertices {k : ℕ} {y x : Vertex d} :
    x ∈ (enlSquare k y).vertices ↔ x ∈ enl 1 k y := by
  rw [IntegerCube.mem_vertices, enl, mem_box]
  have h := two_mul_halfSide_add_one (k + 1)
  refine forall_congr' fun i => ?_
  change center k y i - halfSide (k + 1) ≤ x i ∧
      x i < center k y i - halfSide (k + 1) + ((3 ^ (k + 1) : ℕ) : ℤ) ↔ _
  push_cast
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

/-- The triadic cube of scale `k` containing `z` has the vertices of `cube k z`. -/
theorem mem_triadicCube_idx_iff {k : ℕ} {z x : Vertex d} :
    x ∈ (⟨k, idx k z⟩ : TriadicCube d).vertices ↔ x ∈ cube k z := by
  rw [cube, mem_box]
  simp only [TriadicCube.vertices, TriadicCube.side, Set.mem_setOf_eq]
  have h1 := two_mul_halfSide_add_one k
  refine forall_congr' fun i => ?_
  rw [show center k z i = 3 ^ k * idx k z i from rfl]
  generalize x i - 3 ^ k * idx k z i = a
  rw [abs_mul, abs_two]
  constructor <;> intro h <;> omega

variable {ω : Configuration 2}

/-- If the planar partition cubes of the vertices of `3□'`, `□' = cube k y`, have scale at most `k`,
the square `3□'` is resolved by the planar partition. -/
theorem planarBoxResolved_enlSquare (hP : PlanarPartitionEvent ω) {k : ℕ} {y : Vertex 2}
    (h : ∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) :
    PlanarBoxResolved ω (enlSquare k y) := by
  intro z hz x hx
  have hzE : z ∈ enl 1 k y := mem_enlSquare_vertices.1 hz
  have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le (R := ⟨k, idx k z⟩)
    (planarPartCube_spec hP z).1 (mem_triadicCube_idx_iff.2 (mem_cube_self k z)) (h z hzE) hx
  exact mem_enlSquare_vertices.2 (cube_subset_enl_of_mem hzE (mem_triadicCube_idx_iff.1 hsub))

/-- The cluster of an integer square inside a triadic cube `V` lies in the cluster of `V`. -/
theorem boxClusterVertices_subset_clusterVertices {B : IntegerCube 2} {V : TriadicCube 2}
    (hBV : (↑B.vertices : Set (Vertex 2)) ⊆ V.vertices) :
    boxClusterVertices ω B ⊆ clusterVertices ω V := by
  intro x hx
  have hx' := mem_boxClusterVertices.1 hx
  exact mem_clusterVertices.2 ⟨hBV hx'.1, hx'.2.mono hBV⟩

/-- A vertex of the cluster of a triadic cube `V` lying in `□' = cube k y` belongs to the cluster
of `3□'`, if `3□'` is resolved by the planar partition: its open path to its anchor inside `V`
can only leave `3□'` at distance `3^k` from it, so the window argument applies. -/
theorem mem_boxClusterVertices_of_mem_cube (hP : PlanarPartitionEvent ω) {k : ℕ} {y : Vertex 2}
    {V : TriadicCube 2} (hBr : PlanarBoxResolved ω (enlSquare k y)) {x : Vertex 2}
    (hx : x ∈ clusterVertices ω V) (hxc : x ∈ cube k y) :
    x ∈ boxClusterVertices ω (enlSquare k y) := by
  have hB : (enlSquare k y).size = 3 ^ (k + 1) := rfl
  have hxB : x ∈ (enlSquare k y).vertices := mem_enlSquare_vertices.2 (cube_subset_enl 1 k y hxc)
  have hxC := mem_clusterVertices.1 hx
  have hsub := hBr x hxB
  have hsc := TriadicCube.three_pow_scale_le_size_of_subset_box hsub
  have h := (planarPartCube ω x).reachIn_boxWindow_of_reachIn (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x) hsub (planarPartCube_spec hP x).1 (S := V.vertices) ?_ hxC.2
  · exact mem_boxClusterVertices.2 ⟨hxB,
      (h.mono (Finset.coe_subset.2 ((planarPartCube ω x).boxWindow_subset hsub))).symm⟩
  · intro u hu v _ hv huv
    rw [IntegerCube.mem_vertices] at hu hv
    push Not at hv
    obtain ⟨i, hi⟩ := hv
    refine ⟨i, ?_⟩
    have hui := hu i
    rw [cube, mem_box] at hxc
    have hxi := hxc i
    have hvu := huv i
    have h1 := two_mul_halfSide_add_one k
    have h2 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
    have hsz : (((enlSquare k y).size : ℕ) : ℤ) = 3 * 3 ^ k := by
      rw [hB]
      push_cast
      ring
    have hw100 : 100 * ((3 ^ (planarPartCube ω x).scale / 100 : ℕ) : ℤ) ≤
        3 ^ (planarPartCube ω x).scale := by
      have := Nat.mul_div_le (3 ^ (planarPartCube ω x).scale) 100
      have hc : ((3 ^ (planarPartCube ω x).scale : ℕ) : ℤ) = 3 ^ (planarPartCube ω x).scale := by
        push_cast; rfl
      omega
    have hQ : (3 : ℤ) ^ (planarPartCube ω x).scale ≤ 3 * 3 ^ k := by
      rw [hsz] at hsc
      exact hsc
    rw [hsz] at hui hi
    change center k y i - halfSide (k + 1) ≤ u i ∧
      u i < center k y i - halfSide (k + 1) + 3 * 3 ^ k at hui
    change center k y i - halfSide (k + 1) ≤ v i →
      center k y i - halfSide (k + 1) + 3 * 3 ^ k ≤ v i at hi
    rw [abs_le] at hxi hvu
    rw [le_abs]
    omega

/-- **The Meyers estimate on planar clusters** (Armstrong–Dario, Proposition 3.8, deterministic
part, in dimension two, with the Sobolev inequality of Proposition 3.4 on the clusters of the
triples `3□'` proved). For constants `C_G, K ≥ 0` there are `ε > 0`, `t > 0` and `C < ∞` with the
following property. On the planar partition event, let `V` be a triadic cube containing
`3□ = enl 1 n x₀`, `u` harmonic at the vertices of `𝒞(V) ∩ 3□` whose open neighbours lie in
`𝒞(V)`, the cells `cube (s x) x` of a partition of
`ℤ²` have comparable neighbours and tile `3□`, with `∑_{x ∈ □} (3^{s(x)})^t ≤ K |□|`, and let every
triadic cube `□' = cube k y` containing a cell with `3□' ⊆ 3□` have planar partition cubes of
scale at most `k` at the vertices of `3□'` and `∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G |3□'|`. Then,
with `E = |∇u 1_{𝐚≠0}|²` on `𝒞(V)` (zero outside), `avg_□ E^{1+ε/2} ≤ C (avg_{3□} E)^{1+ε/2}`. -/
theorem planar_meyers {CG K : ℝ} (hCG : 0 ≤ CG) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2) (n : ℕ)
        (x₀ : Vertex 2) (u : Vertex 2 → ℝ) (s : Vertex 2 → ℕ),
        (↑(enl 1 n x₀) : Set (Vertex 2)) ⊆ V.vertices →
        (∀ x ∈ clusterVertices ω V, x ∈ enl 1 n x₀ →
          (∀ y, (openGraph ω).Adj x y → y ∈ clusterVertices ω V) → openLaplacian ω u x = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
            ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω (clusterVertices ω V) u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω (clusterVertices ω V) u) ^ (1 + ε / 2) := by
  obtain ⟨K₀, hK₀, hSobK⟩ := exists_planarBox_sum_sq_le
  obtain ⟨ε, hε, t, ht, C, hC, hM⟩ := meyers_cluster_of_local (d := 2) (by norm_num) hK₀
    (CG := 256 * CG) (by positivity) hK
  refine ⟨ε, hε, t, ht, C, hC, ?_⟩
  intro ω hP V n x₀ u s hV hu hcell hnb hΩ hcubes hmom
  refine hM ω n x₀ (clusterVertices ω V) u s hu hcell hnb hΩ (fun k y hk hsub => ?_) hmom
  obtain ⟨hres, hreach⟩ := hcubes k y hk hsub
  have hBr := planarBoxResolved_enlSquare hP hres
  have hB : (enlSquare k y).size = 3 ^ (k + 1) := rfl
  set B := enlSquare k y with hBdef
  set U' := boxClusterVertices ω B with hU'def
  set P := planarBoxCoarseData hP B hBr with hPdef
  set weight : Vertex 2 → ℝ := fun z => ((3 : ℝ) ^ P.reachScale z) ^ 2 +
    (3 : ℝ) ^ P.pairReachScale z with hweight
  have hw0 : ∀ z, 0 ≤ weight z := fun z => by positivity
  set size : Vertex 2 → ℝ := fun z => weight z ^ ((1 : ℝ) / 4) with hsizedef
  have hsize4 : ∀ z, size z ^ (2 * ((2 : ℕ) : ℝ)) = weight z := fun z => by
    rw [hsizedef, ← Real.rpow_mul (hw0 z)]
    norm_num
  have hU'E : ∀ z ∈ U', z ∈ enl 1 k y := fun z hz =>
    mem_enlSquare_vertices.1 (Finset.mem_filter.1 hz).1
  -- the reach of the planar partition is finite on `3□'`
  have hRHS : ENNReal.ofReal CG * 3 ^ ((k + 1) * 2) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (by norm_num))
  have hfin : ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≠ ∞ := ne_top_of_le_ne_top hRHS hreach
  have hzfin : ∀ z ∈ enl 1 k y, planarReach ω z ≠ ∞ := by
    intro z hz htop
    apply hfin
    refine top_unique ?_
    calc (⊤ : ℝ≥0∞) = planarReach ω z ^ 8 := by rw [htop, ENNReal.top_pow (by norm_num)]
      _ ≤ ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 :=
          Finset.single_le_sum (f := fun z => planarReach ω z ^ 8) (fun _ _ => bot_le) hz
  -- the weight is at most four times the square of the reach
  have hR : ∀ z ∈ U', weight z ≤ 4 * (planarReach ω z).toReal ^ 2 := by
    intro z hz
    have hne := hzfin z (hU'E z hz)
    have h1 : (3 : ℝ) ^ P.reachScale z ≤ (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono hne (three_pow_reachScale_le_planarReach_box hP hBr hz)
      simpa using this
    have h2 : (3 : ℝ) ^ P.pairReachScale z ≤ 3 * (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hne)
        (three_pow_pairReachScale_le_planarReach_box hP hBr z)
      simpa [ENNReal.toReal_mul] using this
    have h3 : 1 ≤ (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono hne (one_le_planarReach hP z)
      simpa using this
    have h0 : 0 ≤ (3 : ℝ) ^ P.reachScale z := by positivity
    have hsq : ((3 : ℝ) ^ P.reachScale z) ^ 2 ≤ (planarReach ω z).toReal ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have hRR : (planarReach ω z).toReal ≤ (planarReach ω z).toReal ^ 2 := by nlinarith
    show ((3 : ℝ) ^ P.reachScale z) ^ 2 + (3 : ℝ) ^ P.pairReachScale z ≤
      4 * (planarReach ω z).toReal ^ 2
    linarith
  have hmomR : ∑ z ∈ U', weight z ^ ((4 : ℕ) : ℝ) ≤ 256 * CG * (3 : ℝ) ^ ((k + 1) * 2) := by
    simp only [Real.rpow_natCast]
    calc ∑ z ∈ U', weight z ^ 4 ≤ ∑ z ∈ U', 256 * (planarReach ω z).toReal ^ 8 :=
          Finset.sum_le_sum fun z hz => by
            calc weight z ^ 4 ≤ (4 * (planarReach ω z).toReal ^ 2) ^ 4 :=
                  pow_le_pow_left₀ (hw0 z) (hR z hz) 4
              _ = 256 * (planarReach ω z).toReal ^ 8 := by ring
      _ ≤ ∑ z ∈ enl 1 k y, 256 * (planarReach ω z).toReal ^ 8 :=
          Finset.sum_le_sum_of_subset_of_nonneg hU'E (fun z _ _ => by positivity)
      _ = 256 * (∑ z ∈ enl 1 k y, planarReach ω z ^ 8).toReal := by
          rw [ENNReal.toReal_sum (fun z hz => ENNReal.pow_ne_top (hzfin z hz)), Finset.mul_sum]
          simp only [ENNReal.toReal_pow]
      _ ≤ 256 * (ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hRHS hreach) (by norm_num)
      _ = 256 * CG * (3 : ℝ) ^ ((k + 1) * 2) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCG, ENNReal.toReal_pow,
            ENNReal.toReal_ofNat]
          ring
  refine ⟨U', size, fun z => Real.rpow_nonneg (hw0 z) _, hU'E, ?_, ?_, ?_, ?_, ?_⟩
  · exact boxClusterVertices_subset_clusterVertices fun x hx =>
      hV (Finset.mem_coe.2 (hsub (mem_enlSquare_vertices.1 hx)))
  · intro z hz w hadj hw
    exact mem_boxClusterVertices.2 (mem_planarBoxCluster_of_adj hP hBr
      (mem_boxClusterVertices.1 hz) hadj (mem_enlSquare_vertices.2 hw))
  · exact fun x hx hxc => mem_boxClusterVertices_of_mem_cube hP hBr hx hxc
  · intro w hw
    have h := hSobK ω hP B (by rw [hB]; positivity) hBr w hw
    rw [lowerSobolevTwo_two]
    have hterm : ∀ z, size z ^ (2 * ((2 : ℕ) : ℝ)) * clusterGradSq ω U' w z ^ ((1 : ℝ) / 2) =
        weight z * gradNormIn (openGraph ω) U' w z := fun z => by
      rw [hsize4, gradNormIn_openGraph_eq, Real.sqrt_eq_rpow]
    rw [Finset.sum_congr rfl fun z _ => hterm z, show (2 : ℝ) / 1 = 2 by norm_num, Real.rpow_two]
    exact h
  · refine (Finset.sum_congr rfl fun z _ => ?_).trans_le hmomR
    rw [hsizedef, ← Real.rpow_mul (hw0 z)]
    congr 1
    push_cast
    ring

end Rigidity.Proofs.Cluster
