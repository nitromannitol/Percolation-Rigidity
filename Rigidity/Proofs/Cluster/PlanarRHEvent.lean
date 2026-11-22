import Rigidity.Proofs.Cluster.PlanarRHPartition

/-!
# The reverse Hölder inequality on a cube whose partition cubes are small, in dimension two

The planar form of Lemma 3.6 of Armstrong and Dario: if the planar partition cubes of the vertices
of the triple `3□` of `□ = cube k x` have scale at most `k - 2` and
`∑_{3□} planarReach^8 ≤ C_G |3□|`, then `PlanarRHCube A₀ ω k x` holds with a deterministic constant
(`planarRHCube_of_scales`).

The cluster `𝒞(3□)` of the integer square of the triple carries the Sobolev inequality of
`exists_planarBox_rh_cube`, and the reverse Hölder inequality holds for the functions harmonic on it
(`reverse_holder_clusterEnergy_local`). A set `C ⊆ 3□` closed under the open edges inside `3□`
contains `𝒞(3□)` as soon as it meets it, since `𝒞(3□)` is connected inside `3□`. A vertex of
`C ∩ □` outside `𝒞(3□)` lies in a part of `C` from which no open edge leaves `3□`: otherwise an open
path from it leaves the square of side `9s` around its partition cube, which lies inside `3□`, and
the anchor property of the partition cube joins it to the anchor inside that square, so the vertex
is in `𝒞(3□)`. On such a part every open edge stays in the part and the harmonic function has zero
energy there, by the Caccioppoli inequality (`clusterGradSq_eq_zero_of_closed`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- **The cluster of the triple with its Sobolev weight** (as `exists_planarBox_meyers_cube`, without
the comparison with the cluster of a larger cube). -/
theorem exists_planarBox_rh_cube :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {CG : ℝ}, 0 ≤ CG → ∀ (ω : Configuration 2), PlanarPartitionEvent ω →
      ∀ (k : ℕ) (y : Vertex 2),
      (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) →
      ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2) →
      ∃ size : Vertex 2 → ℝ, (∀ x, 0 ≤ size x) ∧
        boxClusterVertices ω (enlSquare k y) ⊆ enl 1 k y ∧
        (∀ z ∈ boxClusterVertices ω (enlSquare k y), ∀ w, (openGraph ω).Adj z w →
          w ∈ enl 1 k y → w ∈ boxClusterVertices ω (enlSquare k y)) ∧
        ClusterSobolevTwo ω (boxClusterVertices ω (enlSquare k y)) size CS ∧
        ∑ x ∈ boxClusterVertices ω (enlSquare k y), size x ^ (2 * ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) + 2)) ≤
          256 * CG * (3 : ℝ) ^ ((k + 1) * 2) := by
  obtain ⟨K₀, hK₀, hSobK⟩ := exists_planarBox_sum_sq_le
  refine ⟨K₀, hK₀, fun {CG} hCG ω hP k y hres hreach => ?_⟩
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
  refine ⟨size, fun z => Real.rpow_nonneg (hw0 z) _, hU'E, ?_, ?_, ?_⟩
  · intro z hz w hadj hw
    exact mem_boxClusterVertices.2 (mem_planarBoxCluster_of_adj hP hBr
      (mem_boxClusterVertices.1 hz) hadj (mem_enlSquare_vertices.2 hw))
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



/-- An open walk from a point of `S` to a point outside `S` leaves `S` along an open edge from a
point joined to the start inside `S`. -/
theorem exists_exit_of_walk {S : Set (Vertex 2)} {a b : Vertex 2} (W : (openGraph ω).Walk a b) :
    a ∈ S → b ∉ S → ∃ c c' : Vertex 2, ReachIn ω S a c ∧ (openGraph ω).Adj c c' ∧ c' ∉ S := by
  induction W with
  | nil => exact fun ha hb => absurd ha hb
  | @cons u v w huv q ih =>
    intro hu hw
    by_cases hv : v ∈ S
    · obtain ⟨c, c', hc, hadj, hc'⟩ := ih hv hw
      have huv' : ReachIn ω S u v := ⟨SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil,
        fun z hz => by
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact hu
          · exact hv⟩
      exact ⟨c, c', huv'.trans hc, hadj, hc'⟩
    · exact ⟨u, v, ⟨SimpleGraph.Walk.nil, fun z hz => by
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        exact hz ▸ hu⟩, huv, hv⟩

/-- A set closed under the open edges inside `S` contains every point joined inside `S` to one of
its points. -/
theorem mem_of_reachIn_of_closed {S : Set (Vertex 2)} {C : Finset (Vertex 2)}
    (hcl : ∀ z ∈ C, ∀ w, (openGraph ω).Adj z w → w ∈ S → w ∈ C) {a b : Vertex 2}
    (h : ReachIn ω S a b) (ha : a ∈ C) : b ∈ C := by
  obtain ⟨W, hW⟩ := h
  induction W with
  | nil => exact ha
  | @cons u v w huv q ih =>
    have hvS : v ∈ S := hW v (by simp)
    exact ih (hcl u ha v huv hvS) (fun z hz => hW z (by simp [hz]))

/-- **Zero energy on a closed set.** On a finite set closed under all open edges, a function
harmonic at every point has zero energy, by the Caccioppoli inequality with an arbitrary radius. -/
theorem clusterGradSq_eq_zero_of_closed (D : Finset (Vertex 2))
    (hD : ∀ z ∈ D, ∀ w, (openGraph ω).Adj z w → w ∈ D) (u : Vertex 2 → ℝ)
    (hu : ∀ z ∈ D, openLaplacian ω u z = 0) {z : Vertex 2} (hz : z ∈ D) :
    clusterGradSq ω D u z = 0 := by
  set S := ∑ x ∈ D, clusterGradSq ω D u x with hS
  set M := ∑ x ∈ D.filter (fun x => ¬ (x ∈ D ∧ ∀ y, (nearestNeighborGraph 2).Adj x y → y ∈ D)),
    u x ^ 2 with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hcac : ∀ r : ℝ, 0 < r → S ≤ 8 * (2 : ℕ) / r ^ 2 * M := fun r hr =>
    caccioppoli_cluster ω D D subset_rfl hr (fun x _ z hz hex => by
      obtain ⟨y, hadj, hy⟩ := hex
      exact absurd (hD z hz y hadj) hy) u (fun x hx _ => hu x hx)
  have hS0 : S ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set r : ℝ := Real.sqrt (32 * (M + 1) / S) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr2 : r ^ 2 = 32 * (M + 1) / S := Real.sq_sqrt (by positivity)
    have h := hcac r hr0
    rw [hr2] at h
    have e : 8 * ((2 : ℕ) : ℝ) / (32 * (M + 1) / S) * M = S * (M / (2 * (M + 1))) := by
      field_simp
      ring
    rw [e] at h
    have : M / (2 * (M + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    nlinarith
  have hnn : ∀ x ∈ D, 0 ≤ clusterGradSq ω D u x := fun x _ => clusterGradSq_nonneg ω D u x
  have hS' : S = 0 := le_antisymm hS0 (Finset.sum_nonneg hnn)
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS' z hz

/-- A point of the square of side `9s` around a triadic cube is within `5s` of each of its
vertices. -/
theorem abs_sub_le_five_of_mem_ninefold {Q : TriadicCube 2} {x a : Vertex 2} (hx : x ∈ Q.vertices)
    (ha : a ∈ (↑Q.ninefold.vertices : Set (Vertex 2))) (i : Fin 2) :
    |a i - x i| ≤ 5 * 3 ^ Q.scale := by
  rw [TriadicCube.mem_ninefold] at ha
  have h1 := ha i
  have h2 := Q.abs_sub_center_le hx i
  have h4 := Q.two_mul_ninefoldRadius
  have h5 := abs_sub_le (a i) (Q.center i) (x i)
  rw [abs_sub_comm (Q.center i) (x i)] at h5
  linarith

/-- The square of side `9s` around the partition cube of a vertex of `□` lies in the triple of `□`
when the partition cube has scale at most `k - 2`. -/
theorem ninefold_subset_enl {k : ℕ} {x₀ z : Vertex 2} (hz : z ∈ cube k x₀) {Q : TriadicCube 2}
    (hzQ : z ∈ Q.vertices) (hQ : Q.scale + 2 ≤ k) :
    (↑Q.ninefold.vertices : Set (Vertex 2)) ⊆ ↑(enl 1 k x₀) := by
  intro y hy
  rw [Finset.mem_coe, enl, mem_box]
  rw [cube, mem_box] at hz
  intro i
  have h1 := abs_sub_le_five_of_mem_ninefold hzQ hy i
  have h2 := hz i
  have h3 : (3 : ℤ) ^ (Q.scale + 2) ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hQ
  have h4 := two_mul_halfSide_add_one k
  have h5 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have h6 : (0 : ℤ) < 3 ^ Q.scale := by positivity
  have h7 : (3 : ℤ) ^ (Q.scale + 2) = 9 * 3 ^ Q.scale := by ring
  calc |y i - center k x₀ i| ≤ |y i - z i| + |z i - center k x₀ i| := abs_sub_le _ _ _
    _ ≤ halfSide (k + 1) := by rw [h5]; linarith

/-- **A vertex of `□` joined to the outside of `3□` is in the cluster of the triple.** -/
theorem mem_boxCluster_of_exit (hP : PlanarPartitionEvent ω) {k : ℕ} {x₀ z w : Vertex 2}
    (hz : z ∈ cube k x₀) (hQ : (planarPartCube ω z).scale + 2 ≤ k)
    (W : (openGraph ω).Walk z w) (hw : w ∉ enl 1 k x₀) :
    z ∈ planarBoxCluster ω (enlSquare k x₀) := by
  set Q := planarPartCube ω z with hQdef
  set N : Set (Vertex 2) := ↑Q.ninefold.vertices with hN
  have hzQ : z ∈ Q.vertices := (planarPartCube_spec hP z).1
  have hNsub := ninefold_subset_enl hz hzQ hQ
  have hzN : z ∈ N := Q.vertices_subset_ninefold hzQ
  have hwN : w ∉ N := fun h => hw (hNsub h)
  obtain ⟨c, c', hzc, hadj, hc'⟩ := exists_exit_of_walk W hzN hwN
  have hspec := Q.planarAnchor_spec (planarPartCube_meshed hP z).1 (planarPartCube_large hP z)
  -- the displacement of `c` from `z`
  have hc'' : ¬ ∀ i, |c' i - Q.center i| ≤ Q.ninefoldRadius := fun h =>
    hc' (TriadicCube.mem_ninefold.2 h)
  push Not at hc''
  obtain ⟨i, hi⟩ := hc''
  have h1 := abs_sub_le_one_of_openGraph_adj hadj i
  have h2 := Q.abs_sub_center_le hzQ i
  have h3 := Q.two_mul_ninefoldRadius
  have h4 : ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ 3 ^ Q.scale := by
    have : (3 ^ Q.scale / 100 : ℕ) ≤ 3 ^ Q.scale := Nat.div_le_self _ _
    exact_mod_cast this
  have h5 : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  have hfar : ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ |c i - z i| := by
    have t1 := abs_sub_le (c' i) (c i) (Q.center i)
    have t2 := abs_sub_le (c i) (z i) (Q.center i)
    rw [abs_sub_comm (c' i) (c i)] at t1
    linarith
  have hreach : ReachIn ω N (Q.planarAnchor ω) z := by
    rcases le_or_gt (z i + ((3 ^ Q.scale / 100 : ℕ) : ℤ)) (c i) with h | h
    · exact hspec.2.2 z c i hzc h
    · have h' : c i + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ z i := by
        rcases abs_cases (c i - z i) with ⟨h6, _⟩ | ⟨h6, _⟩ <;> linarith
      exact (hspec.2.2 c z i hzc.symm h').trans hzc.symm
  refine ⟨mem_enlSquare_vertices.2 (cube_subset_enl 1 k x₀ hz), ?_⟩
  exact (hreach.symm).mono fun y hy => by
    rw [Finset.mem_coe, mem_enlSquare_vertices]
    exact hNsub hy

/-- The constant of the reverse Hölder inequality on the cubes of the triple with small partition
cubes. -/
noncomputable def planarRHConst (CS CG : ℝ) : ℝ :=
  8 * (2 : ℕ) * CS * (256 * CG) ^ (2 / ((((2 : ℕ) : ℝ) + 2) * lowerSobolevTwo 2)) *
    (3 : ℝ) ^ ((2 : ℕ) + 2)

/-- **The reverse Hölder inequality on a cube with small partition cubes** (planar form of
Lemma 3.6 of Armstrong and Dario, for every set of the triple closed under its open edges). -/
theorem planarRHCube_of_scales :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {CG : ℝ}, 0 ≤ CG → ∀ (ω : Configuration 2), PlanarPartitionEvent ω →
      ∀ (k : ℕ) (x₀ : Vertex 2), (∀ z ∈ enl 1 k x₀, (planarPartCube ω z).scale + 2 ≤ k) →
      ∑ z ∈ enl 1 k x₀, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2) →
      PlanarRHCube (planarRHConst CS CG) ω k x₀ := by
  obtain ⟨CS, hCS, hbox⟩ := exists_planarBox_rh_cube
  refine ⟨CS, hCS, fun {CG} hCG ω hP k x₀ hres hreach => ?_⟩
  have hres' : ∀ z ∈ enl 1 k x₀, (planarPartCube ω z).scale ≤ k := fun z hz => by
    have := hres z hz; omega
  obtain ⟨size, hsize, hU'E, hclosed, hSob, hmom⟩ := hbox hCG ω hP k x₀ hres' hreach
  set B := enlSquare k x₀ with hB
  set U' := boxClusterVertices ω B with hU'
  have hBr := planarBoxResolved_enlSquare hP hres'
  intro C hC hcl u hu
  -- vertices of `C ∩ □` outside `U'` carry no energy
  have hZ : ∀ z ∈ C, z ∈ cube k x₀ → z ∉ U' → clusterEnergy ω C u z = 0 := by
    intro z hzC hzc hzU
    set D := C.filter (fun a => ReachIn ω ↑C z a) with hD
    have hzD : z ∈ D := Finset.mem_filter.2 ⟨hzC, ⟨SimpleGraph.Walk.nil, fun a ha => by
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ha
      rw [ha]; exact hzC⟩⟩
    have hDC : D ⊆ C := Finset.filter_subset _ _
    have hDcl : ∀ a ∈ D, ∀ w, (openGraph ω).Adj a w → w ∈ D := by
      intro a ha w hadj
      obtain ⟨haC, hza⟩ := Finset.mem_filter.1 ha
      by_cases hw : w ∈ enl 1 k x₀
      · have hwC := hcl a haC w hadj hw
        refine Finset.mem_filter.2 ⟨hwC, hza.trans ⟨SimpleGraph.Walk.cons hadj
          SimpleGraph.Walk.nil, fun b hb => ?_⟩⟩
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact haC
        · exact hwC
      · exfalso
        obtain ⟨W, -⟩ := hza
        exact hzU (mem_boxClusterVertices.2 (mem_boxCluster_of_exit hP hzc
          (hres z (cube_subset_enl 1 k x₀ hzc)) (W.concat hadj) hw))
    have hharm : ∀ a ∈ D, openLaplacian ω u a = 0 := fun a ha =>
      hu a (hDC ha) fun w hw => hDC (hDcl a ha w hw)
    have h0 := clusterGradSq_eq_zero_of_closed D hDcl u hharm hzD
    unfold clusterEnergy
    rw [if_pos hzC, ← h0]
    unfold clusterGradSq
    congr 2
    refine Finset.filter_congr fun w hw => ?_
    have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hw
    exact ⟨fun hwC => hDcl z hzD w hadj, fun hwD => hDC hwD⟩
  have hA0 : 0 ≤ planarRHConst CS CG := by unfold planarRHConst; positivity
  have hRHS0 : 0 ≤ planarRHConst CS CG * avg (enl 1 k x₀) (fun z =>
      clusterEnergy ω C u z ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1))) ^ ((((2 : ℕ) : ℝ) + 1) / (2 : ℕ)) :=
    mul_nonneg hA0 (Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun z _ =>
      Real.rpow_nonneg (clusterEnergy_nonneg _ _ _ z) _) (Nat.cast_nonneg _)) _)
  by_cases hmeet : ∃ a ∈ C, a ∈ U'
  · obtain ⟨a, haC, haU⟩ := hmeet
    -- `U' ⊆ C`
    have hU'C : U' ⊆ C := by
      intro b hb
      have ha' := mem_boxClusterVertices.1 haU
      have hb' := mem_boxClusterVertices.1 hb
      have hab : ReachIn ω ↑B.vertices a b :=
        ha'.2.trans ((reachIn_planarAnchor_of_boxResolved hP hBr ha'.1 hb'.1).trans hb'.2.symm)
      exact mem_of_reachIn_of_closed (S := ↑B.vertices) (fun z hz w hadj hw => hcl z hz w hadj
        (mem_enlSquare_vertices.1 hw)) hab haC
    have hrh := reverse_holder_clusterEnergy_local ω (by norm_num : 0 < 2) U' u k x₀
      (fun z hz _ hall => hu z (hU'C hz) fun w hw => hU'C (hall w hw)) U' hU'E subset_rfl hclosed
      (fun z hz _ => hz) size hsize hCS (by positivity : (0 : ℝ) ≤ 256 * CG) hSob hmom
    have hnum : avg (cube k x₀) (clusterEnergy ω C u) ≤ avg (cube k x₀) (clusterEnergy ω U' u) := by
      unfold avg
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun z hz => ?_) (Nat.cast_nonneg _)
      by_cases hzU : z ∈ U'
      · apply le_of_eq
        unfold clusterEnergy
        rw [if_pos (hU'C hzU), if_pos hzU]
        unfold clusterGradSq
        congr 2
        refine Finset.filter_congr fun w hw => ?_
        have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hw
        have hwE : w ∈ enl 1 k x₀ := mem_enl_of_near_cube hz fun i => by
          rw [abs_sub_comm]; exact abs_sub_le_one_of_openGraph_adj hadj i
        exact ⟨fun hwC => hclosed z hzU w hadj hwE, fun hwU => hU'C hwU⟩
      · by_cases hzC : z ∈ C
        · rw [hZ z hzC hz hzU]
          exact clusterEnergy_nonneg _ _ _ z
        · unfold clusterEnergy
          rw [if_neg hzC]
          exact clusterEnergy_nonneg _ _ _ z
    have hden : avg (enl 1 k x₀) (fun z =>
        clusterEnergy ω U' u z ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1))) ≤
        avg (enl 1 k x₀) (fun z => clusterEnergy ω C u z ^ (((2 : ℕ) : ℝ) / ((2 : ℕ) + 1))) := by
      unfold avg
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun z _ => ?_) (Nat.cast_nonneg _)
      refine Real.rpow_le_rpow (clusterEnergy_nonneg _ _ _ z) ?_ (by positivity)
      unfold clusterEnergy
      by_cases hzU : z ∈ U'
      · rw [if_pos hzU, if_pos (hU'C hzU)]
        exact clusterGradSq_le_of_subset ω hU'C u z
      · rw [if_neg hzU]
        split_ifs
        · exact clusterGradSq_nonneg _ _ _ _
        · exact le_rfl
    refine hnum.trans (hrh.trans ?_)
    change planarRHConst CS CG * _ ≤ _
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg
      fun z _ => Real.rpow_nonneg (clusterEnergy_nonneg _ _ _ z) _) (Nat.cast_nonneg _)) hden
      (by positivity)) hA0
  · push Not at hmeet
    have h0 : avg (cube k x₀) (clusterEnergy ω C u) = 0 := by
      unfold avg
      rw [Finset.sum_eq_zero fun z hz => ?_, zero_div]
      by_cases hzC : z ∈ C
      · exact hZ z hzC hz (hmeet z hzC)
      · unfold clusterEnergy; rw [if_neg hzC]
    rw [h0]
    exact hRHS0

end Rigidity.Proofs.Cluster
