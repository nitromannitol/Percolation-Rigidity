import Rigidity.Proofs.Percolation.PlanarFlatnessNu
import Rigidity.Proofs.Cluster.Caccioppoli
import Rigidity.Proofs.Cluster.ReverseHolder

/-!
# The Caccioppoli inequality from `□_{n+1}` to `□_n` on planar clusters

For a resolved cube `□_{n+1}` (on the partition event), `n ≥ 1`, and a function `w` on its cluster,
harmonic at the vertices whose lattice neighbours lie in `□_{n+1}`, the Caccioppoli inequality
(Armstrong and Dario, Lemma 3.5) on the vertices of `C_*(□_{n+1})` interior to `□_{n+1}`, whose
open edges leave this set only at distance at least `3^n - 1` from `□_n`, gives for every
constant `c`

`B_{□_n}(w, w) ≤ 16 (3^n - 1)⁻² ∑_{x ∈ C_*(□_{n+1})} (w(x) - c)²`,

`B_{□_n}` the Dirichlet form of the open edges of `C_*(□_n)`. This is the second inequality of
display (5.39) of Armstrong and Dario, in dimension two.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

theorem mem_vertices_zero_iff {m : ℕ} {x : Vertex 2} :
    x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices ↔ ∀ i, |2 * x i| < (3 : ℤ) ^ m := by
  change (∀ i, |2 * (x i - (3 : ℤ) ^ m * (0 : Vertex 2) i)| < (3 : ℤ) ^ m) ↔ _
  simp

/-- The vertices of `□_n` are interior to `□_{n+1}`. -/
theorem isInterior_of_mem_central {n : ℕ} {x : Vertex 2}
    (hx : x ∈ (⟨n, 0⟩ : TriadicCube 2).vertices) : (⟨n + 1, 0⟩ : TriadicCube 2).IsInterior x := by
  intro y hy
  rw [mem_vertices_zero_iff] at hx ⊢
  intro i
  have h1 := hx i
  have h2 := hy i
  have h3 : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at h2
  constructor <;> nlinarith

/-- A vertex of `□_n` is at sup-distance at least `3^n - 1` from every vertex within distance two
of a vertex outside `□_{n+1}`. -/
theorem le_supDist_of_far {n : ℕ} {x z y y' : Vertex 2}
    (hx : x ∈ (⟨n, 0⟩ : TriadicCube 2).vertices) (hzy : ∀ i, |z i - y i| ≤ 1)
    (hyy' : ∀ i, |y i - y' i| ≤ 1) (hy' : y' ∉ (⟨n + 1, 0⟩ : TriadicCube 2).vertices) :
    (3 : ℝ) ^ n - 1 ≤ (Rigidity.Proofs.Cluster.supDist x z : ℝ) := by
  rw [mem_vertices_zero_iff] at hx hy'
  push Not at hy'
  obtain ⟨i, hi⟩ := hy'
  have h1 := hx i
  have h2 := hzy i
  have h3 := hyy' i
  set N : ℤ := 3 ^ n with hN
  have hN1 : (1 : ℤ) ≤ N := one_le_pow₀ (by norm_num)
  rw [pow_succ, ← hN] at hi
  have key : N - 1 ≤ ((x i - z i).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    rw [abs_lt] at h1
    rw [abs_le] at h2 h3
    rcases le_abs'.1 hi with h | h <;> rcases abs_cases (x i - z i) with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
      omega
  have hle : (x i - z i).natAbs ≤ Rigidity.Proofs.Cluster.supDist x z :=
    Rigidity.Proofs.Cluster.natAbs_le_supDist x z i
  have key' : (N : ℝ) - 1 ≤ ((x i - z i).natAbs : ℝ) := by
    have h := Int.cast_le (R := ℝ) |>.mpr key
    rw [Int.cast_natCast, Int.cast_sub, Int.cast_one] at h
    exact h
  have hle' : ((x i - z i).natAbs : ℝ) ≤ (Rigidity.Proofs.Cluster.supDist x z : ℝ) := by
    exact_mod_cast hle
  have hNr : (N : ℝ) = (3 : ℝ) ^ n := by rw [hN]; push_cast; rfl
  rw [← hNr]
  linarith

/-- The Laplacian of the extension of a harmonic function at an interior vertex of the cluster. -/
theorem openLaplacian_clusterExtend_of_interior (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {w : ClusterFun ω U} (hw : w ∈ clusterHarmonic ω U) {x : Vertex 2}
    (hx : x ∈ clusterVertices ω U) (hint : U.IsInterior x) :
    openLaplacian ω (clusterExtend ω U w) x = 0 := by
  have h0 := (mem_clusterHarmonic.1 hw) ⟨x, hx⟩ hint
  rw [clusterLaplacianAt_apply] at h0
  have e1 : ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x y.1 then w y - w ⟨x, hx⟩ else 0) =
      ∑ y ∈ clusterVertices ω U, (if (openGraph ω).Adj x y then
        clusterExtend ω U w y - clusterExtend ω U w x else 0) := by
    rw [← Finset.sum_coe_sort (clusterVertices ω U)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [clusterExtend_apply_of_mem w y.2, clusterExtend_apply_of_mem w hx]
  rw [e1, ← Finset.sum_filter] at h0
  have e2 : (clusterVertices ω U).filter (fun y => (openGraph ω).Adj x y) =
      (openGraph ω).neighborFinset x := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => h.2, fun h => ⟨mem_clusterVertices_of_adj hP hU hx hint h, h⟩⟩
  rw [e2] at h0
  exact h0

/-- The interior vertices of `C_*(□_{n+1})` leave this set by an open edge only far from `□_n`. -/
theorem caccioppoli_dist (hP : PlanarPartitionEvent ω) {n : ℕ}
    (hU : PlanarResolved ω ⟨n + 1, 0⟩) :
    ∀ x ∈ clusterVertices ω ⟨n, 0⟩, ∀ z ∈ (clusterVertices ω ⟨n + 1, 0⟩).filter
        (fun x => (⟨n + 1, 0⟩ : TriadicCube 2).IsInterior x),
      (∃ y, (openGraph ω).Adj z y ∧ y ∉ (clusterVertices ω ⟨n + 1, 0⟩).filter
        (fun x => (⟨n + 1, 0⟩ : TriadicCube 2).IsInterior x)) →
      (3 : ℝ) ^ n - 1 ≤ (Rigidity.Proofs.Cluster.supDist x z : ℝ) := by
  rintro x hx z hz ⟨y, hzy, hyU'⟩
  obtain ⟨hzC, hzint⟩ := Finset.mem_filter.1 hz
  have hyC := mem_clusterVertices_of_adj hP hU hzC hzint hzy
  have hyint : ¬ (⟨n + 1, 0⟩ : TriadicCube 2).IsInterior y :=
    fun h => hyU' (Finset.mem_filter.2 ⟨hyC, h⟩)
  unfold TriadicCube.IsInterior at hyint
  push Not at hyint
  obtain ⟨y', hyy', hy'⟩ := hyint
  exact le_supDist_of_far (mem_clusterVertices.1 hx).1
    (fun i => by
      rw [abs_sub_comm]
      exact Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hzy) i) hyy' hy'

/-- Harmonicity at the interior vertices, in the form of the Caccioppoli inequality. -/
theorem caccioppoli_harm (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {w : ClusterFun ω U} (hw : w ∈ clusterHarmonic ω U) (c : ℝ) :
    ∀ x ∈ (clusterVertices ω U).filter (fun x => U.IsInterior x),
      (∀ y, (openGraph ω).Adj x y → y ∈ (clusterVertices ω U).filter
        (fun x => U.IsInterior x)) →
      openLaplacian ω (fun y => clusterExtend ω U w y - c) x = 0 := by
  intro x hx _
  obtain ⟨hxC, hxint⟩ := Finset.mem_filter.1 hx
  rw [Rigidity.Proofs.Cluster.openLaplacian_sub_const]
  exact openLaplacian_clusterExtend_of_interior hP hU hw hxC hxint

/-- The Dirichlet form on `C_*(□_n)` of the restriction is at most the sum of the squared gradients
on the vertices of `C_*(□_n)` inside a larger set. -/
theorem clusterForm_restrict_le_sum_clusterGradSq {U V : TriadicCube 2} {S : Finset (Vertex 2)}
    (hVS : clusterVertices ω V ⊆ S) (w : ClusterFun ω U) (c : ℝ) :
    clusterForm ω V (clusterRestrictExt V w) (clusterRestrictExt V w) ≤
      ∑ x ∈ clusterVertices ω V, Rigidity.Proofs.Cluster.clusterGradSq ω S
        (fun y => clusterExtend ω U w y - c) x := by
  rw [clusterForm_self_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Rigidity.Proofs.Cluster.clusterGradSq]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hext : ∀ y ∈ clusterVertices ω V,
      clusterExtend ω V (clusterRestrictExt V w) y = clusterExtend ω U w y := by
    intro y hy
    rw [clusterExtend_apply_of_mem _ hy]
    rfl
  rw [← Finset.sum_filter]
  have e : ∀ y ∈ (clusterVertices ω V).filter (fun y => (openGraph ω).Adj x y),
      (clusterExtend ω V (clusterRestrictExt V w) x -
          clusterExtend ω V (clusterRestrictExt V w) y) *
        (clusterExtend ω V (clusterRestrictExt V w) x -
          clusterExtend ω V (clusterRestrictExt V w) y) =
      ((clusterExtend ω U w x - c) - (clusterExtend ω U w y - c)) ^ 2 := by
    intro y hy
    rw [hext x hx, hext y (Finset.mem_filter.1 hy).1]
    ring
  rw [Finset.sum_congr rfl e]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun _ _ _ => sq_nonneg _
  obtain ⟨hyV, hadj⟩ := Finset.mem_filter.1 hy
  exact Finset.mem_filter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hadj, hVS hyV⟩

/-- **The Caccioppoli inequality from `□_{n+1}` to `□_n`** (Armstrong and Dario, Lemma 3.5, as in
display (5.39), in dimension two). -/
theorem clusterForm_restrict_le_caccioppoli (hP : PlanarPartitionEvent ω) {n : ℕ} (hn : 1 ≤ n)
    (hU : PlanarResolved ω ⟨n + 1, 0⟩) {w : ClusterFun ω ⟨n + 1, 0⟩}
    (hw : w ∈ clusterHarmonic ω ⟨n + 1, 0⟩) (c : ℝ) :
    clusterForm ω ⟨n, 0⟩ (clusterRestrictExt ⟨n, 0⟩ w) (clusterRestrictExt ⟨n, 0⟩ w) ≤
      16 / ((3 : ℝ) ^ n - 1) ^ 2 * ∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
        (clusterExtend ω ⟨n + 1, 0⟩ w x - c) ^ 2 := by
  have hVU : (⟨n, 0⟩ : TriadicCube 2).vertices ⊆ (⟨n + 1, 0⟩ : TriadicCube 2).vertices :=
    fun x hx => isInterior_of_mem_central hx x (fun i => by simp)
  have hV'U' : clusterVertices ω ⟨n, 0⟩ ⊆ (clusterVertices ω ⟨n + 1, 0⟩).filter
      (fun x => (⟨n + 1, 0⟩ : TriadicCube 2).IsInterior x) := fun x hx =>
    Finset.mem_filter.2 ⟨clusterVertices_subset hVU hx,
      isInterior_of_mem_central (mem_clusterVertices.1 hx).1⟩
  have h3n : (1 : ℝ) < 3 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hr : (0 : ℝ) < 3 ^ n - 1 := by linarith
  have hcac := Rigidity.Proofs.Cluster.caccioppoli_cluster ω _ _ hV'U' hr
    (caccioppoli_dist hP hU) _ (caccioppoli_harm hP hU hw c)
  have hR : ∑ x ∈ ((clusterVertices ω ⟨n + 1, 0⟩).filter
        (fun x => (⟨n + 1, 0⟩ : TriadicCube 2).IsInterior x)).filter
        (fun x => ¬ (x ∈ clusterVertices ω ⟨n, 0⟩ ∧
          ∀ y, (nearestNeighborGraph 2).Adj x y → y ∈ clusterVertices ω ⟨n, 0⟩)),
        (clusterExtend ω (⟨n + 1, 0⟩ : TriadicCube 2) w x - c) ^ 2 ≤
      ∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
        (clusterExtend ω (⟨n + 1, 0⟩ : TriadicCube 2) w x - c) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans
      (Finset.filter_subset _ _)) fun x _ _ => sq_nonneg _
  have h16 : (8 * ((2 : ℕ) : ℝ) / ((3 : ℝ) ^ n - 1) ^ 2) = 16 / ((3 : ℝ) ^ n - 1) ^ 2 := by
    norm_num
  rw [h16] at hcac
  exact (clusterForm_restrict_le_sum_clusterGradSq hV'U' w c).trans
    (hcac.trans (mul_le_mul_of_nonneg_left hR (by positivity)))

end Rigidity.Percolation
