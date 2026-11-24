import Rigidity.Proofs.Green.DarioGuApproxInputs
import PercolationClusterHomogenization.Proofs.Cluster.MeyersPlanarBox
import Rigidity.Proofs.Corrector.PlanarShiftedAnchor
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseBound
import Rigidity.Proofs.S2.PlanarVarianceMoments
import Rigidity.Proofs.S2.WeightedResamplingTonelli
import Rigidity.Proofs.S3.Divergence
import Rigidity.Proofs.Section5.Peierls

/-!
# The weak Poincaré inequality on balls of the planar infinite cluster

The deterministic part of the weak form of Proposition 2.7 of Dario–Gu (`ClusterPoincareTwo`) in
dimension two, from the Sobolev inequality of Armstrong–Dario (Proposition 3.4, `s = 2`) on the
cluster `C(B)` of the triple `B = 3□` of the triadic cube `□` of scale `m` containing `y`
(`exists_planarBox_sum_sq_le`):

if the partition cubes of the vertices of `B` have scale at most `m - 3` and
`Σ_{z ∈ B} (ρ(z)² + 3ρ(z))² ≤ A` for the reach `ρ` of the planar partition, then for `2R ≤ 3^m`
and `ρ' ≥ 4 · 3^m`

`Σ_{x ∈ 𝒞_∞ ∩ B_R(y)} (u(x) - (u)_{𝒞_∞ ∩ B_R(y)})² ≤ K A ‖∇u‖²_{L²(𝒞_∞ ∩ B_{ρ'}(y))}`

(`sum_sq_sub_finAvg_clusterBall_le`). The vertices of `𝒞_∞ ∩ B_R(y)` are joined to the anchors of
their partition cubes inside the ninefold enlargements of these cubes (Armstrong–Dario, Lemma 2.8,
`TriadicCube.reachIn_anchor_of_infinite`), hence inside `B`, so they belong to `C(B)`; the vertices
of `C(B)` are joined to anchors, which belong to `𝒞_∞`, and lie in `B_{ρ'}(y)`.
-/

open Finset LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
open Rigidity.Proofs.Section5
open scoped ENNReal

namespace Rigidity.Green

/-- The average minimizes the sum of squares: `Σ_U (u - (u)_U)² ≤ Σ_U (u - a)²`. -/
theorem sum_sq_sub_finAvg_le (U : Finset (Vertex 2)) (u : Vertex 2 → ℝ) (a : ℝ) :
    ∑ x ∈ U, (u x - finAvg U u) ^ 2 ≤ ∑ x ∈ U, (u x - a) ^ 2 := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (0 : ℝ) < U.card := by exact_mod_cast hne.card_pos
  have hsum : ∑ x ∈ U, (u x - finAvg U u) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, finAvg]
    field_simp
    ring
  have e : ∑ x ∈ U, (u x - a) ^ 2 = ∑ x ∈ U, (u x - finAvg U u) ^ 2 +
      2 * (finAvg U u - a) * ∑ x ∈ U, (u x - finAvg U u) + U.card * (finAvg U u - a) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have : ∑ x ∈ U, (u x - a) ^ 2 = ∑ x ∈ U, ((u x - finAvg U u) ^ 2 +
        2 * (finAvg U u - a) * (u x - finAvg U u) + (finAvg U u - a) ^ 2) :=
      Finset.sum_congr rfl fun x _ => by ring
    rw [this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [e, hsum, mul_zero, add_zero]
  have : 0 ≤ (U.card : ℝ) * (finAvg U u - a) ^ 2 := by positivity
  linarith

/-- The vertices within `3^m` of `y` in every coordinate lie in the triple `enl 1 m y`. -/
theorem mem_enl_of_abs_sub_le {m : ℕ} {x y : Vertex 2} (h : ∀ i, |x i - y i| ≤ 3 ^ m) :
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

/-- The vertices of the triple `enl 1 m y` are at distance less than `4 · 3^m` from `y`. -/
theorem latticeDist_lt_of_mem_enl {m : ℕ} {x y : Vertex 2} (h : x ∈ enl 1 m y) :
    latticeDist x y < 4 * 3 ^ m := by
  have hy := mem_cube_self m y
  rw [cube, mem_box] at hy
  rw [enl, mem_box] at h
  have h3 := two_mul_halfSide_add_one m
  have h3' := two_mul_halfSide_add_one (m + 1)
  have hco : ∀ i, |((x i : ℤ) : ℝ) - y i| < 2 * 3 ^ m := by
    intro i
    have a1 := h i
    have a2 := hy i
    have := abs_sub_le (x i) (center m y i) (y i)
    rw [abs_sub_comm (center m y i) (y i)] at this
    have hint : |x i - y i| < 2 * 3 ^ m := by
      have : (3 : ℤ) ^ (m + 1) = 3 * 3 ^ m := by ring
      linarith
    have hr : ((|x i - y i| : ℤ) : ℝ) < ((2 * 3 ^ m : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at hr
    exact hr
  have hsq := latticeDist_sq x y
  have h0 := latticeDist_nonneg x y
  have a0 := hco 0
  have a1 := hco 1
  have b0 := abs_nonneg ((x 0 : ℝ) - y 0)
  have b1 := abs_nonneg ((x 1 : ℝ) - y 1)
  have hle : latticeDist x y ≤ |(x 0 : ℝ) - y 0| + |(x 1 : ℝ) - y 1| := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    rw [hsq]
    nlinarith [sq_abs ((x 0 : ℝ) - y 0), sq_abs ((x 1 : ℝ) - y 1)]
  linarith

/-- **The weak Poincaré inequality on a ball, deterministic part.** -/
theorem sum_sq_sub_finAvg_clusterBall_le :
    ∃ KS : ℝ, 0 ≤ KS ∧ ∀ (ω : Configuration 2) (hP : PlanarPartitionEvent ω)
      (h : HasUniqueInfiniteOpenComponent ω) (y : Vertex 2) (m : ℕ) (A R ρ : ℝ),
      (∀ z ∈ enl 1 m y, (planarPartCube ω z).scale + 3 ≤ m) →
      (∑ z ∈ enl 1 m y, (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2 ≤ ENNReal.ofReal A) →
      2 * R ≤ 3 ^ m → 4 * 3 ^ m ≤ ρ → ∀ u : Vertex 2 → ℝ,
        ∑ x ∈ clusterBall (uniqueInfiniteComponent h) y R,
            (u x - finAvg (clusterBall (uniqueInfiniteComponent h) y R) u) ^ 2 ≤
          KS * A * gradEnergy ω (clusterBall (uniqueInfiniteComponent h) y ρ) u := by
  obtain ⟨KS, hKS, hsob⟩ := exists_planarBox_sum_sq_le
  refine ⟨KS, hKS, ?_⟩
  intro ω hP h y m A R ρ hscale hreach hRm hρm u
  classical
  set K := uniqueInfiniteComponent h with hK
  set B := enlSquare m y with hB
  have hBr : PlanarBoxResolved ω B :=
    planarBoxResolved_enlSquare hP fun z hz => by have := hscale z hz; omega
  have hBsize : 0 < B.size := by rw [hB, enlSquare_size]; positivity
  set S := boxClusterVertices ω B with hS
  have hSB : ∀ z ∈ S, z ∈ enl 1 m y := fun z hz =>
    mem_enlSquare_vertices.1 ((mem_boxClusterVertices.1 hz).1)
  -- the reach is finite on `B`
  have hfin : ∀ z ∈ enl 1 m y, planarReach ω z ≠ ⊤ := by
    intro z hz htop
    have hle : (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2 ≤ ENNReal.ofReal A :=
      (Finset.single_le_sum (f := fun z => (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2)
        (fun _ _ => zero_le) hz).trans hreach
    rw [htop] at hle
    simp at hle
  -- the vertices of `C(B)` are in `𝒞_∞ ∩ B_ρ(y)`
  have hSball : ∀ z ∈ S, z ∈ clusterBall K y ρ := by
    intro z hz
    have hzc := mem_boxClusterVertices.1 hz
    rw [mem_clusterBall]
    refine ⟨?_, (latticeDist_lt_of_mem_enl (hSB z hz)).trans_le hρm⟩
    rw [hK, mem_uniqueInfiniteComponent_iff]
    have hinf := Rigidity.Corrector.infinite_planarCoarseAnchor hP z
    have hr : (openGraph ω).Reachable z (planarCoarseAnchor ω z) := hzc.2.reachable
    change ((openGraph ω).connectedComponentMk z).supp.Infinite
    rw [SimpleGraph.ConnectedComponent.eq.mpr hr]
    exact hinf
  -- the vertices of `𝒞_∞ ∩ B_R(y)` are in `C(B)`
  have hballS : ∀ x ∈ clusterBall K y R, x ∈ S := by
    intro x hx
    rw [mem_clusterBall] at hx
    set Q := planarPartCube ω x with hQ
    have hxQ : x ∈ Q.vertices := (planarPartCube_spec hP x).1
    have hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite := by
      have := (mem_uniqueInfiniteComponent_iff h x).1 hx.1
      exact this
    have hspec := TriadicCube.planarAnchor_spec (planarPartCube_meshed hP x).1
      (planarPartCube_large hP x)
    have hreachQ := TriadicCube.reachIn_anchor_of_infinite hspec.2.2 hxQ hinf
    have hxB : ∀ i, |x i - y i| ≤ 3 ^ m := by
      intro i
      have h1 := latticeDist_ge_abs x y i
      have h2 : |((x i - y i : ℤ) : ℝ)| < (3 : ℝ) ^ m := by
        push_cast
        have : (2 : ℝ) * R ≤ 3 ^ m := by exact_mod_cast hRm
        have h3m : (0 : ℝ) < 3 ^ m := by positivity
        linarith [hx.2]
      have h3 : ((|x i - y i| : ℤ) : ℝ) < ((3 ^ m : ℤ) : ℝ) := by push_cast at h2 ⊢; exact h2
      exact_mod_cast h3.le
    have hnine : (↑Q.ninefold.vertices : Set (Vertex 2)) ⊆ ↑B.vertices := by
      intro z hz
      rw [TriadicCube.mem_ninefold] at hz
      rw [Finset.mem_coe, hB, mem_enlSquare_vertices]
      apply mem_enl_of_abs_sub_le
      intro i
      have hk := hscale x (mem_enl_of_abs_sub_le hxB)
      have hc := TriadicCube.abs_sub_center_le hxQ i
      have hz' := hz i
      have hr := Q.two_mul_ninefoldRadius
      have hpow : (27 : ℤ) * 3 ^ Q.scale ≤ 3 ^ m := by
        calc (27 : ℤ) * 3 ^ Q.scale = 3 ^ (Q.scale + 3) := by ring
          _ ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) hk
      have hxy := hxB i
      have hR2 : 2 * |x i - y i| ≤ 3 ^ m := by
        have h1 := latticeDist_ge_abs x y i
        have h2 : (2 : ℝ) * |((x i - y i : ℤ) : ℝ)| ≤ 3 ^ m := by
          push_cast
          have : (2 : ℝ) * R ≤ 3 ^ m := by exact_mod_cast hRm
          have h3m : (0 : ℝ) < 3 ^ m := by positivity
          linarith [hx.2]
        have h3 : ((2 * |x i - y i| : ℤ) : ℝ) ≤ ((3 ^ m : ℤ) : ℝ) := by push_cast at h2 ⊢; exact h2
        exact_mod_cast h3
      have t1 := abs_sub_le (z i) (Q.center i) (x i)
      have t2 := abs_sub_le (z i) (x i) (y i)
      rw [abs_sub_comm (Q.center i) (x i)] at t1
      have hs3 : (0 : ℤ) < 3 ^ Q.scale := by positivity
      linarith
    have hxBv : x ∈ B.vertices := by
      rw [hB, mem_enlSquare_vertices]
      exact mem_enl_of_abs_sub_le hxB
    rw [hS, mem_boxClusterVertices]
    exact mem_planarBoxCluster_of_reachIn hP hBr hxBv hxBv (hreachQ.mono hnine).symm
  -- the Sobolev inequality on `C(B)`
  set c := finAvg S u with hc
  set w : Vertex 2 → ℝ := fun x => u x - c with hw
  have hw0 : ∑ x ∈ S, w x = 0 := by
    rcases S.eq_empty_or_nonempty with hSe | hne
    · rw [hSe, Finset.sum_empty]
    · have hcard : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
      simp only [hw, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hc, finAvg]
      field_simp
      ring
  have hS1 := hsob ω hP B hBsize hBr w hw0
  set W : Vertex 2 → ℝ := fun z => ((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).reachScale z) ^ 2 +
    (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z with hW
  set g : Vertex 2 → ℝ := fun z => gradNormIn (openGraph ω) S w z with hg
  have hW0 : ∀ z, 0 ≤ W z := fun z => by positivity
  -- the weights
  have hWle : ∀ z ∈ S, W z ≤ (planarReach ω z).toReal ^ 2 + 3 * (planarReach ω z).toReal := by
    intro z hz
    have hz' := hfin z (hSB z hz)
    have h1 := three_pow_reachScale_le_planarReach_box hP hBr hz
    have h2 := three_pow_pairReachScale_le_planarReach_box hP hBr z
    have h1' : (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).reachScale z ≤ (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono hz' h1
      simpa using this
    have h2' : (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z ≤
        3 * (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hz') h2
      simpa [ENNReal.toReal_mul] using this
    have h0 : (0 : ℝ) ≤ (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).reachScale z := by positivity
    simp only [hW]
    nlinarith
  have hWsum : ∑ z ∈ S, W z ^ 2 ≤ A := by
    have h1 : ∑ z ∈ S, W z ^ 2 ≤ ∑ z ∈ enl 1 m y,
        ((planarReach ω z).toReal ^ 2 + 3 * (planarReach ω z).toReal) ^ 2 := by
      calc ∑ z ∈ S, W z ^ 2 ≤ ∑ z ∈ S,
            ((planarReach ω z).toReal ^ 2 + 3 * (planarReach ω z).toReal) ^ 2 :=
            Finset.sum_le_sum fun z hz => pow_le_pow_left₀ (hW0 z) (hWle z hz) 2
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => hSB z hz)
            fun z _ _ => sq_nonneg _
    refine h1.trans ?_
    have h2 : ∑ z ∈ enl 1 m y, ((planarReach ω z).toReal ^ 2 + 3 * (planarReach ω z).toReal) ^ 2 =
        (∑ z ∈ enl 1 m y, (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2).toReal := by
      rw [ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun z hz => ?_
        have hz' := hfin z hz
        rw [ENNReal.toReal_pow, ENNReal.toReal_add (ENNReal.pow_ne_top hz')
          (ENNReal.mul_ne_top (by norm_num) hz'), ENNReal.toReal_pow, ENNReal.toReal_mul]
        norm_num
      · intro z hz
        have := hfin z hz
        exact ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top this,
          ENNReal.mul_ne_top (by norm_num) this⟩)
    rw [h2]
    by_cases hA : 0 ≤ A
    · exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hreach)
        ENNReal.ofReal_ne_top).2 hreach |>.trans (by rw [ENNReal.toReal_ofReal hA])
    · push Not at hA
      rw [ENNReal.ofReal_of_nonpos hA.le, nonpos_iff_eq_zero] at hreach
      rw [hreach, ENNReal.toReal_zero]
      exfalso
      have hB0 : (enl 1 m y).Nonempty := ⟨y, mem_enl_of_abs_sub_le fun i => by simp⟩
      obtain ⟨z, hz⟩ := hB0
      have h0 := (Finset.sum_eq_zero_iff.1 hreach) z hz
      have hz1 : (1 : ℝ≥0∞) ≤ planarReach ω z := by
        have := Rigidity.Proofs.Regularity.three_pow_planarPartCube_scale_le_planarReach hP z
        exact (one_le_pow₀ (by norm_num)).trans this
      have : (planarReach ω z ^ 2 + 3 * planarReach ω z) ^ 2 ≠ 0 := by
        apply pow_ne_zero
        apply ne_of_gt
        calc (0 : ℝ≥0∞) < 1 := one_pos
          _ ≤ planarReach ω z ^ 2 := one_le_pow₀ hz1
          _ ≤ planarReach ω z ^ 2 + 3 * planarReach ω z := le_self_add
      exact this h0
  -- the gradients
  have hg2 : ∀ z ∈ S, g z ^ 2 ≤ (∑ z' ∈ (clusterBall K y ρ).filter (fun z' => (openGraph ω).Adj z z'),
      |u z' - u z|) ^ 2 := by
    intro z hz
    have hgz : g z ^ 2 = (1 / 2) * ∑ y' ∈ S, if (openGraph ω).Adj z y' then (w z - w y') ^ 2 else 0 := by
      simp only [hg, gradNormIn]
      rw [Real.sq_sqrt (by
        apply mul_nonneg (by norm_num)
        exact Finset.sum_nonneg fun y' _ => by split_ifs <;> positivity)]
    rw [hgz]
    have h1 : ∑ y' ∈ S, (if (openGraph ω).Adj z y' then (w z - w y') ^ 2 else 0) =
        ∑ y' ∈ S.filter (fun y' => (openGraph ω).Adj z y'), |u y' - u z| ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y' _ => ?_
      split_ifs
      · simp only [hw, sq_abs]; ring
      · rfl
    rw [h1]
    have h2 : ∑ y' ∈ S.filter (fun y' => (openGraph ω).Adj z y'), |u y' - u z| ^ 2 ≤
        (∑ y' ∈ S.filter (fun y' => (openGraph ω).Adj z y'), |u y' - u z|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _
    have h3 : ∑ y' ∈ S.filter (fun y' => (openGraph ω).Adj z y'), |u y' - u z| ≤
        ∑ z' ∈ (clusterBall K y ρ).filter (fun z' => (openGraph ω).Adj z z'), |u z' - u z| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => abs_nonneg _
      intro y' hy'
      rw [Finset.mem_filter] at hy' ⊢
      exact ⟨hSball y' hy'.1, hy'.2⟩
    have h4 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) h3 2
    have h5 : 0 ≤ ∑ y' ∈ S.filter (fun y' => (openGraph ω).Adj z y'), |u y' - u z| ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have hgsum : ∑ z ∈ S, g z ^ 2 ≤ gradEnergy ω (clusterBall K y ρ) u := by
    refine (Finset.sum_le_sum hg2).trans ?_
    unfold gradEnergy
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => hSball z hz)
      (fun _ _ _ => sq_nonneg _)
  -- conclusion
  have hCS : (∑ z ∈ S, W z * g z) ^ 2 ≤ (∑ z ∈ S, W z ^ 2) * ∑ z ∈ S, g z ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S W g
  have hball : ∑ x ∈ clusterBall K y R, (u x - finAvg (clusterBall K y R) u) ^ 2 ≤
      ∑ x ∈ S, w x ^ 2 := by
    refine (sum_sq_sub_finAvg_le _ u c).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hballS fun _ _ _ => sq_nonneg _
  have hgE := gradEnergy_nonneg ω (clusterBall K y ρ) u
  calc ∑ x ∈ clusterBall K y R, (u x - finAvg (clusterBall K y R) u) ^ 2
      ≤ ∑ x ∈ S, w x ^ 2 := hball
    _ ≤ KS * (∑ z ∈ S, W z * g z) ^ 2 := hS1
    _ ≤ KS * ((∑ z ∈ S, W z ^ 2) * ∑ z ∈ S, g z ^ 2) := mul_le_mul_of_nonneg_left hCS hKS
    _ ≤ KS * (A * gradEnergy ω (clusterBall K y ρ) u) := by
        apply mul_le_mul_of_nonneg_left _ hKS
        exact mul_le_mul hWsum hgsum (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          ((Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hWsum)
    _ = KS * A * gradEnergy ω (clusterBall K y ρ) u := by ring

end Rigidity.Green
