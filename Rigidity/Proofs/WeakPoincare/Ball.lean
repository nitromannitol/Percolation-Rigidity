import Rigidity.Proofs.WeakPoincare.Sobolev
import PercolationClusterHomogenization.Proofs.Cluster.MeyersPartitionBox
import PercolationClusterHomogenization.Proofs.Partition.Paths

/-!
# The weak Poincaré inequality on a ball of the infinite cluster, deterministic part

The deterministic part of the weak Poincaré inequality on Euclidean balls of `𝒞_∞` in every
dimension `d ≥ 2`, from the Sobolev inequality of Armstrong–Dario (Proposition 3.4, `s = 2`) on the
cluster `C(B)` of the triple `B = 3□` of the triadic cube `□` of scale `m` containing `y`
(`exists_clusterSobolevTwo_box`, with Hölder's inequality: `sum_sq_le_of_clusterSobolevTwo`):

on the partition event of the partition into good cubes, if the partition cubes of the vertices of
`B` have scale at most `m - 3`, the reach of the partition is dominated by `ss` and
`Σ_{z ∈ B} ss(z)^{d(d+2)} ≤ A`, then for `2R ≤ 3^m` and `ρ ≥ 2d · 3^m`

`Σ_{x ∈ 𝒞_∞ ∩ B_R(y)} (u(x) - (u)_{𝒞_∞ ∩ B_R(y)})² ≤ K A^{2/d} Σ_{edges of 𝒞_∞ ∩ B_ρ(y)} |∇u|²`

(`sum_sq_sub_finAvg_clusterBall_le`). The vertices of `𝒞_∞ ∩ B_R(y)` are joined to the anchors of
their partition cubes inside the parent cube and a small cube around them (Armstrong–Dario,
Lemma 2.8, `reachable_partitionAnchor_of_infinite`), hence inside `B`, so they belong to `C(B)`;
the vertices of `C(B)` are joined to anchors, which belong to `𝒞_∞`, and lie in `B_ρ(y)`.
This is the argument of the planar case (`Rigidity.Green.sum_sq_sub_finAvg_clusterBall_le`).
-/

open Finset LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped ENNReal

namespace Rigidity.WeakPoincare

variable {d : ℕ}

/-- The vertices within `3^m` of `y` in every coordinate lie in the triple `enl 1 m y`. -/
theorem mem_enl_of_abs_sub_le {m : ℕ} {x y : Vertex d} (h : ∀ i, |x i - y i| ≤ 3 ^ m) :
    x ∈ enl 1 m y := by
  have hy := mem_cube_self m y
  rw [cube, mem_box] at hy
  rw [enl, mem_box]
  intro i
  have h1 := hy i
  have h2 := h i
  have h3 := two_mul_halfSide_add_one m
  have h4 : halfSide (m + 1) = 3 * halfSide m + 1 := rfl
  have := abs_sub_le (x i) (y i) (center m y i)
  linarith

/-- The coordinates of a vertex of the triple `enl 1 m y` differ from those of `y` by less than
`2 · 3^m`. -/
theorem abs_sub_lt_of_mem_enl {m : ℕ} {x y : Vertex d} (h : x ∈ enl 1 m y) (i : Fin d) :
    |x i - y i| < 2 * 3 ^ m := by
  have hy := mem_cube_self m y
  rw [cube, mem_box] at hy
  rw [enl, mem_box] at h
  have h3 := two_mul_halfSide_add_one m
  have h3' := two_mul_halfSide_add_one (m + 1)
  have a1 := h i
  have a2 := hy i
  have := abs_sub_le (x i) (center m y i) (y i)
  rw [abs_sub_comm (center m y i) (y i)] at this
  have : (3 : ℤ) ^ (m + 1) = 3 * 3 ^ m := by ring
  linarith

/-- The side of the partition cube of `z` is at most the reach of the partition at `z`. -/
theorem three_pow_scale_le_partitionReach {ω : Configuration d} (hP : PartitionEvent ω)
    (z : Vertex d) : (3 : ℝ≥0∞) ^ (partitionCube ω z).scale ≤ partitionReach ω z := by
  unfold partitionReach
  have hz : z ∈ cubeAt z 0 := fun i => by simp
  exact le_iSup₂_of_le (f := fun (Q : TriadicCube d) _ => (3 : ℝ≥0∞) ^ Q.scale) (partitionCube ω z)
    ⟨(partitionCube_spec hP z).2, Finset.mem_coe.1
      (TriadicCube.cubeAt_subset_thicken (mem_partitionCube hP z) (Nat.zero_le _) hz)⟩ le_rfl

/-- A power of `3` below the reach of the partition is below every real dominating the reach. -/
theorem three_pow_le_of_partitionReach_le {ω : Configuration d} {z : Vertex d} {n : ℕ} {a : ℝ}
    (h1 : (3 : ℝ≥0∞) ^ n ≤ partitionReach ω z) (h2 : partitionReach ω z ≤ ENNReal.ofReal a) :
    (3 : ℝ) ^ n ≤ a := by
  have h := h1.trans h2
  rw [show (3 : ℝ≥0∞) ^ n = ENNReal.ofReal ((3 : ℝ) ^ n) by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num] at h
  exact (ENNReal.ofReal_le_ofReal_iff' |>.1 h).resolve_right (by
    intro h'
    have := pow_pos (by norm_num : (0 : ℝ) < 3) n
    linarith)

/-- **The weak Poincaré inequality on a ball, deterministic part**, in every dimension `d ≥ 2`. -/
theorem sum_sq_sub_finAvg_clusterBall_le (hd : 2 ≤ d) :
    ∃ KS : ℝ, 0 ≤ KS ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω)
      (h : HasUniqueInfiniteOpenComponent ω) (y : Vertex d) (m : ℕ) (A R ρ : ℝ)
      (ss : Vertex d → ℝ),
      (∀ z ∈ enl 1 m y, (partitionCube ω z).scale + 3 ≤ m) →
      (∀ z, partitionReach ω z ≤ ENNReal.ofReal (ss z)) →
      (∑ z ∈ enl 1 m y, ss z ^ (d * (d + 2)) ≤ A) →
      2 * R ≤ 3 ^ m → 2 * d * 3 ^ m ≤ ρ → ∀ u : Vertex d → ℝ,
        ∑ x ∈ clusterBall (uniqueInfiniteComponent h) y R,
            (u x - finAvg (clusterBall (uniqueInfiniteComponent h) y R) u) ^ 2 ≤
          KS * A ^ (2 / (d : ℝ)) *
            nbrEnergy ω (clusterBall (uniqueInfiniteComponent h) y ρ) u := by
  have hd0 : 0 < d := by omega
  obtain ⟨K0, hK0, hsob⟩ := exists_clusterSobolevTwo_box hd
  refine ⟨K0, hK0, ?_⟩
  intro ω hP h y m A R ρ ss hscale hreach hA hRm hρm u
  classical
  set K := uniqueInfiniteComponent h with hK
  set B := enlSquare m y with hB
  have hBr : PartitionBoxResolved ω B :=
    partitionBoxResolved_enlSquare hP fun z hz => by have := hscale z hz; omega
  have hBsize : 0 < B.size := by rw [hB, enlSquare_size]; positivity
  set S := partitionBoxCluster ω B with hS
  have hSB : ∀ z ∈ S, z ∈ enl 1 m y := fun z hz =>
    mem_enlSquare_vertices.1 (mem_partitionBoxCluster.1 hz).1
  have hss1 : ∀ z, 1 ≤ ss z := fun z =>
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)).trans
      (three_pow_le_of_partitionReach_le (three_pow_scale_le_partitionReach hP z) (hreach z))
  -- the vertices of `C(B)` are in `𝒞_∞ ∩ B_ρ(y)`
  have hSball : ∀ z ∈ S, z ∈ clusterBall K y ρ := by
    intro z hz
    have hzc := mem_partitionBoxCluster.1 hz
    rw [mem_clusterBall]
    refine ⟨?_, ?_⟩
    · rw [hK, mem_uniqueInfiniteComponent_iff]
      have hinf := infinite_supp_partitionAnchor hd0 hP z
      have hr : (openGraph ω).Reachable z (partitionAnchor ω z) := by
        refine hzc.2.mono ?_
        intro a b hab
        exact hab.1
      change ((openGraph ω).connectedComponentMk z).supp.Infinite
      rw [SimpleGraph.ConnectedComponent.eq.mpr hr]
      exact hinf
    · have h1 := latticeDist_lt_of_abs_lt hd0 (x := z) (y := y) (a := 2 * 3 ^ m) fun i => by
        have h2 := abs_sub_lt_of_mem_enl (hSB z hz) i
        have h3 : ((|z i - y i| : ℤ) : ℝ) < ((2 * 3 ^ m : ℤ) : ℝ) := by exact_mod_cast h2
        push_cast at h3
        exact h3
      calc latticeDist z y < d * (2 * 3 ^ m) := h1
        _ = 2 * d * 3 ^ m := by ring
        _ ≤ ρ := hρm
  -- the vertices of `𝒞_∞ ∩ B_R(y)` are in `C(B)`
  have hballS : ∀ x ∈ clusterBall K y R, x ∈ S := by
    intro x hx
    rw [mem_clusterBall] at hx
    set Q := partitionCube ω x with hQ
    have hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite :=
      (mem_uniqueInfiniteComponent_iff h x).1 hx.1
    have hreachQ := reachable_partitionAnchor_of_infinite hd0 hP hinf
    have hxy : ∀ i, 2 * |x i - y i| < 3 ^ m := by
      intro i
      have h1 := (abs_sub_le_latticeDist x y i).trans_lt hx.2
      have h2 : (2 : ℝ) * |((x i - y i : ℤ) : ℝ)| < ((3 ^ m : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h2
    have hxE : x ∈ enl 1 m y := mem_enl_of_abs_sub_le fun i => by
      have h1 := hxy i
      have h2 := abs_nonneg (x i - y i)
      linarith
    have hxm : Q.scale + 3 ≤ m := hscale x hxE
    have hreg : Q.parent.vertices ∪ cubeAt x (3 ^ Q.scale / 2) ⊆ ↑B.vertices := by
      rintro z (hz | hz)
      · have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le
          (R := ⟨m - 1, idx (m - 1) x⟩) (Q.vertices_subset_parent (mem_partitionCube hP x))
          (mem_triadicCube_idx_iff.2 (mem_cube_self (m - 1) x))
          (show Q.scale + 1 ≤ m - 1 by omega) hz
        have hzc := mem_triadicCube_idx_iff.1 hsub
        have hxc := mem_cube_self (m - 1) x
        rw [cube, mem_box] at hzc hxc
        rw [Finset.mem_coe, hB, mem_enlSquare_vertices]
        refine mem_enl_of_abs_sub_le fun i => ?_
        have hzi := hzc i
        have hxi := hxc i
        have h5 := two_mul_halfSide_add_one (m - 1)
        have hpow : (3 : ℤ) ^ m = 3 * 3 ^ (m - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        have t1 := abs_sub_le (z i) (center (m - 1) x i) (x i)
        rw [abs_sub_comm (center (m - 1) x i) (x i)] at t1
        have t2 := abs_sub_le (z i) (x i) (y i)
        have hx2 := hxy i
        have hpos : (0 : ℤ) < 3 ^ (m - 1) := by positivity
        linarith
      · have hz' : ∀ i, |z i - x i| ≤ ((3 ^ Q.scale / 2 : ℕ) : ℤ) := hz
        have hn : ((3 ^ Q.scale / 2 : ℕ) : ℤ) ≤ ((3 ^ Q.scale : ℕ) : ℤ) :=
          Int.ofNat_le.2 (Nat.div_le_self _ _)
        have e : ((3 ^ Q.scale : ℕ) : ℤ) = 3 ^ Q.scale := by push_cast; ring
        have hpow : (27 : ℤ) * 3 ^ Q.scale ≤ 3 ^ m := by
          calc (27 : ℤ) * 3 ^ Q.scale = 3 ^ (Q.scale + 3) := by ring
            _ ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) hxm
        rw [Finset.mem_coe, hB, mem_enlSquare_vertices]
        refine mem_enl_of_abs_sub_le fun i => ?_
        have t2 := abs_sub_le (z i) (x i) (y i)
        have hx2 := hxy i
        have hzi := hz' i
        have hpos : (0 : ℤ) < 3 ^ Q.scale := by positivity
        linarith
    have hxB : x ∈ B.vertices := by
      rw [hB, mem_enlSquare_vertices]
      exact hxE
    exact mem_partitionBoxCluster.2 ⟨hxB, reachable_openIn_mono hreg hreachQ⟩
  -- the Sobolev inequality on `C(B)`
  have hSob := hsob ω hP B hBsize hBr
  set size : Vertex d → ℝ := fun z =>
    (3 : ℝ) ^ (partitionBoxCoarseData hd0 hP B hBr).reachScale z with hsize
  have hsize0 : ∀ z, 0 ≤ size z := fun z => by positivity
  have hsizele : ∀ z ∈ S, size z ≤ ss z := fun z hz =>
    three_pow_le_of_partitionReach_le
      (three_pow_reachScale_le_partitionReach_box hd0 hP hBr hz) (hreach z)
  have hAS : ∑ z ∈ S, size z ^ (d * (d + 2)) ≤ A := by
    calc ∑ z ∈ S, size z ^ (d * (d + 2)) ≤ ∑ z ∈ S, ss z ^ (d * (d + 2)) :=
          Finset.sum_le_sum fun z hz => pow_le_pow_left₀ (hsize0 z) (hsizele z hz) _
      _ ≤ ∑ z ∈ enl 1 m y, ss z ^ (d * (d + 2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => hSB z hz)
            fun z _ _ => pow_nonneg (zero_le_one.trans (hss1 z)) _
      _ ≤ A := hA
  have hA0 : 0 ≤ A := (Finset.sum_nonneg fun z _ => pow_nonneg (hsize0 z) _).trans hAS
  set c := finAvg S u with hc
  set w : Vertex d → ℝ := fun x => u x - c with hw
  have hw0 : ∑ x ∈ S, w x = 0 := by
    rcases S.eq_empty_or_nonempty with hSe | hne
    · rw [hSe, Finset.sum_empty]
    · have hcard : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
      simp only [hw, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hc, finAvg]
      field_simp
      ring
  have hmain := sum_sq_le_of_clusterSobolevTwo hd0 (size := size) hsize0 hK0 hSob hAS w hw0
  -- the gradients
  have hgrad : ∑ x ∈ S, clusterGradSq ω S w x ≤ nbrEnergy ω (clusterBall K y ρ) u := by
    have h1 : ∀ x ∈ S, clusterGradSq ω S w x ≤
        ∑ z ∈ (clusterBall K y ρ).filter (fun z => (openGraph ω).Adj x z), (u z - u x) ^ 2 := by
      intro x _
      unfold clusterGradSq
      have e : ∀ y', (w x - w y') ^ 2 = (u y' - u x) ^ 2 := fun y' => by simp only [hw]; ring
      simp only [e]
      have hsub : ((openGraph ω).neighborFinset x).filter (· ∈ S) ⊆
          (clusterBall K y ρ).filter (fun z => (openGraph ω).Adj x z) := by
        intro z hz
        rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hz
        exact Finset.mem_filter.2 ⟨hSball z hz.2, hz.1⟩
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun z => (u z - u x) ^ 2) fun _ _ _ => sq_nonneg _
      have h3 : 0 ≤ ∑ z ∈ ((openGraph ω).neighborFinset x).filter (· ∈ S), (u z - u x) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
    calc ∑ x ∈ S, clusterGradSq ω S w x
        ≤ ∑ x ∈ S, ∑ z ∈ (clusterBall K y ρ).filter (fun z => (openGraph ω).Adj x z),
            (u z - u x) ^ 2 := Finset.sum_le_sum h1
      _ ≤ nbrEnergy ω (clusterBall K y ρ) u := by
          unfold nbrEnergy
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => hSball x hx)
            fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- conclusion
  calc ∑ x ∈ clusterBall K y R, (u x - finAvg (clusterBall K y R) u) ^ 2
      ≤ ∑ x ∈ clusterBall K y R, (u x - c) ^ 2 := sum_sq_sub_finAvg_le _ u c
    _ ≤ ∑ x ∈ S, w x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hballS fun _ _ _ => sq_nonneg _
    _ ≤ K0 * A ^ (2 / (d : ℝ)) * ∑ x ∈ S, clusterGradSq ω S w x := hmain
    _ ≤ K0 * A ^ (2 / (d : ℝ)) * nbrEnergy ω (clusterBall K y ρ) u :=
        mul_le_mul_of_nonneg_left hgrad (mul_nonneg hK0 (Real.rpow_nonneg hA0 _))

end Rigidity.WeakPoincare
