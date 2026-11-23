import Rigidity.Proofs.Dirichlet.PlanarClusterEdges
import Rigidity.Proofs.Cluster.PlanarSobolevTwo

/-!
# The Poincaré inequality on the planar cluster for functions vanishing on the boundary

Let `U` be a triadic cube and `U'` its parent, with all partition cubes of the vertices of `U'` of
scale at most `k ≤ scale(U)`, and let `f` vanish off the interior vertices of `C_*(U)`. Then `f`
vanishes on `C_*(U') \ C_*(U)`, which contains the anchors of the partition cubes of the vertices
of `U' \ U`, hence at least `8 · 9^{scale(U) - k}` vertices
(`card_le_mul_card_sdiff_clusterVertices`). The mean-zero Sobolev inequality on `C_*(U')`
(Armstrong and Dario, Proposition 3.4, `s = 2`, for the planar partition,
`exists_planar_sum_sq_le`) applied to `f − f̄` and the Cauchy–Schwarz inequality give
`Σ_{C_*(U)} f² ≤ (1 + (9/8) 9^k) K Σ_{C_*(U')} W² Σ_{open edges of C_*(U)} (∇f)²`
with `W = (3^ρ)² + 3^{ρ'} ≤ 2 · 9^k`, so
`Σ_{C_*(U)} f² ≤ 4 (1 + (9/8) 9^k) K 9^{scale(U)+1} 81^k Σ_{open edges of C_*(U)} (∇f)²`
(`exists_planar_sum_sq_le_of_eq_zero`). This is Proposition 3.4 of the source with `s = 2` for
functions vanishing on the boundary, as used in the proofs of Lemma 6.3 and Proposition 6.1, with
the size of the partition cubes entering through their maximum.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

theorem gradNormIn_sub_const (G : SimpleGraph (Vertex 2)) (S : Finset (Vertex 2))
    (f : Vertex 2 → ℝ) (c : ℝ) (x : Vertex 2) :
    gradNormIn G S (fun y => f y - c) x = gradNormIn G S f x := by
  unfold gradNormIn
  congr 2
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- The reach scales are at most the largest scale of the partition cubes of the domain. -/
theorem reachScale_le_of_forall {U : TriadicCube 2} (hP : PlanarPartitionEvent ω)
    (hU : PlanarResolved ω U) {k : ℕ}
    (hk : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ k) (z : Vertex 2) :
    (planarCoarseData hP U hU).reachScale z ≤ k ∧
      (planarCoarseData hP U hU).pairReachScale z ≤ k := by
  constructor
  · refine Finset.sup_le fun x hx => ?_
    have hxU : x ∈ U.vertices :=
      (mem_clusterVertices.1 (Finset.mem_filter.1 hx).1).1
    exact hk x hxU
  · refine Finset.sup_le fun q hq => ?_
    have hq' := (Finset.mem_filter.1 hq).1
    rw [CoarseData.edgesAcross, Finset.mem_filter, Finset.mem_product] at hq'
    exact hk q.1 ((U.mem_toIntegerCube_vertices q.1).1 hq'.1.1)

/-- An open neighbour of an interior vertex of the cluster of a resolved cube is in the cluster. -/
theorem mem_clusterVertices_of_adj (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {x y : Vertex 2} (hx : x ∈ clusterVertices ω U)
    (hyU : y ∈ U.vertices) (hadj : (openGraph ω).Adj x y) : y ∈ clusterVertices ω U := by
  have hxC := mem_clusterVertices.1 hx
  refine mem_clusterVertices.2 (mem_planarCubeCluster_of_reachIn hP hU hyU hxC.1 ?_)
  refine ReachIn.trans ⟨SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil, fun v hv => ?_⟩ hxC.2
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact hyU
  · exact hxC.1

/-- The cluster vertices of `U' \ U` number at least `|U' \ U| / 9^k`. -/
theorem card_le_mul_card_sdiff_clusterVertices (hP : PlanarPartitionEvent ω)
    {U U' : TriadicCube 2} (hU' : PlanarResolved ω U')
    {k : ℕ} (hkU : k ≤ U.scale) (hk : ∀ x ∈ U'.vertices, (planarPartCube ω x).scale ≤ k) :
    (U'.toIntegerCube.vertices \ U.toIntegerCube.vertices).card ≤
      9 ^ k * (clusterVertices ω U' \ clusterVertices ω U).card := by
  set A := U'.toIntegerCube.vertices \ U.toIntegerCube.vertices
  set f : Vertex 2 → Vertex 2 := planarCoarseAnchor ω
  have himage : A.image f ⊆ clusterVertices ω U' \ clusterVertices ω U := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨hxU', hxU⟩ := Finset.mem_sdiff.1 hx
    rw [U'.mem_toIntegerCube_vertices] at hxU'
    rw [U.mem_toIntegerCube_vertices] at hxU
    have hmem := ((planarPartCube ω x).planarAnchor_spec (planarPartCube_meshed hP x).1
      (planarPartCube_large hP x)).1
    refine Finset.mem_sdiff.2 ⟨mem_clusterVertices.2
      (planarAnchor_mem_planarCubeCluster hP hU' hxU'), fun h => ?_⟩
    -- the partition cube of `x` meets `U`, hence lies in `U`, which contains `x`
    have hfU := (mem_clusterVertices.1 h).1
    have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le hmem hfU
      ((hk x hxU').trans hkU)
    exact hxU (hsub (planarPartCube_spec hP x).1)
  have hfib : ∀ a ∈ A.image f, (A.filter fun x => f x = a).card ≤ 9 ^ k := by
    intro a ha
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 ha
    have hx₀U' : x₀ ∈ U'.vertices :=
      (U'.mem_toIntegerCube_vertices x₀).1 (Finset.mem_sdiff.1 hx₀).1
    -- every vertex with the same anchor lies in the partition cube of `x₀`
    have hsub : A.filter (fun x => f x = f x₀) ⊆
        (planarPartCube ω x₀).toIntegerCube.vertices := by
      intro x hx
      obtain ⟨-, hfx⟩ := Finset.mem_filter.1 hx
      have ha1 := ((planarPartCube ω x).planarAnchor_spec (planarPartCube_meshed hP x).1
        (planarPartCube_large hP x)).1
      have ha0 := ((planarPartCube ω x₀).planarAnchor_spec (planarPartCube_meshed hP x₀).1
        (planarPartCube_large hP x₀)).1
      change (planarPartCube ω x).planarAnchor ω = (planarPartCube ω x₀).planarAnchor ω at hfx
      rw [hfx] at ha1
      have e1 := planarPartCube_eq_of_mem hP ha1
      have e0 := planarPartCube_eq_of_mem hP ha0
      rw [e0] at e1
      rw [TriadicCube.mem_toIntegerCube_vertices, e1]
      exact (planarPartCube_spec hP x).1
    refine (Finset.card_le_card hsub).trans ?_
    rw [IntegerCube.card_vertices]
    change (3 ^ (planarPartCube ω x₀).scale) ^ 2 ≤ 9 ^ k
    rw [← pow_mul, show (9 : ℕ) ^ k = 3 ^ (2 * k) by rw [pow_mul]; norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by have := hk x₀ hx₀U'; omega)
  calc A.card = ∑ a ∈ A.image f, (A.filter fun x => f x = a).card :=
        Finset.card_eq_sum_card_image f A
    _ ≤ ∑ _a ∈ A.image f, 9 ^ k := Finset.sum_le_sum hfib
    _ = 9 ^ k * (A.image f).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 9 ^ k * (clusterVertices ω U' \ clusterVertices ω U).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himage)

/-- The lattice neighbours of an interior vertex lie in the cube. -/
theorem TriadicCube.add_sub_unit_mem_of_isInterior {U : TriadicCube 2} {x : Vertex 2}
    (hx : U.IsInterior x) (k : Fin 2) : x + unit k ∈ U.vertices ∧ x - unit k ∈ U.vertices := by
  constructor
  · refine hx _ fun i => ?_
    by_cases hik : i = k <;> simp [unit, hik]
  · refine hx _ fun i => ?_
    by_cases hik : i = k <;> simp [unit, hik]

/-- The edge energy of `f` on the open edges of `C_*(U')` reduces to `C_*(U)` when `f` vanishes
off the interior vertices of `C_*(U)`. -/
theorem sum_edges_le_of_support (hP : PlanarPartitionEvent ω) {U U' : TriadicCube 2}
    (hUU' : U.vertices ⊆ U'.vertices) (hU : PlanarResolved ω U) (f : Vertex 2 → ℝ)
    (hf : ∀ x, ¬(x ∈ clusterVertices ω U ∧ U.IsInterior x) → f x = 0) :
    ∑ z ∈ clusterVertices ω U', ∑ k : Fin 2,
        (if z + unit k ∈ clusterVertices ω U' ∧ (openGraph ω).Adj z (z + unit k) then
          (f (z + unit k) - f z) ^ 2 else 0) ≤
      ∑ z ∈ clusterVertices ω U, ∑ k : Fin 2,
        (if z + unit k ∈ clusterVertices ω U ∧ (openGraph ω).Adj z (z + unit k) then
          (f (z + unit k) - f z) ^ 2 else 0) := by
  set C := clusterVertices ω U'
  set C₀ := clusterVertices ω U
  have hC₀C : C₀ ⊆ C := clusterVertices_subset hUU'
  have hint : ∀ x, U.IsInterior x → ∀ k : Fin 2,
      x + unit k ∈ U.vertices ∧ x - unit k ∈ U.vertices := fun x hx k =>
    TriadicCube.add_sub_unit_mem_of_isInterior hx k
  have hterm : ∀ z ∈ C, ∀ k : Fin 2,
      (if z + unit k ∈ C ∧ (openGraph ω).Adj z (z + unit k) then (f (z + unit k) - f z) ^ 2
        else 0) ≤
      if z ∈ C₀ then (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
        (f (z + unit k) - f z) ^ 2 else 0) else 0 := by
    intro z hz k
    by_cases h1 : z + unit k ∈ C ∧ (openGraph ω).Adj z (z + unit k)
    · rw [if_pos h1]
      by_cases hz0 : z ∈ C₀ ∧ z + unit k ∈ C₀
      · rw [if_pos hz0.1, if_pos ⟨hz0.2, h1.2⟩]
      · -- one endpoint is outside `C_*(U)`, so both values vanish
        have hfz : f z = 0 := by
          refine hf z fun ⟨hzC, hzI⟩ => hz0 ⟨hzC, ?_⟩
          exact mem_clusterVertices_of_adj hP hU hzC (hint z hzI k).1 h1.2
        have hfz' : f (z + unit k) = 0 := by
          refine hf _ fun ⟨hzC, hzI⟩ => hz0 ⟨?_, hzC⟩
          have hzU : z ∈ U.vertices := by
            have := (hint _ hzI k).2
            rwa [add_sub_cancel_right] at this
          exact mem_clusterVertices_of_adj hP hU hzC hzU h1.2.symm
        rw [hfz, hfz', sub_zero, sq, mul_zero]
        split_ifs <;> exact le_rfl
    · rw [if_neg h1]
      split_ifs <;> positivity
  calc ∑ z ∈ C, ∑ k : Fin 2,
        (if z + unit k ∈ C ∧ (openGraph ω).Adj z (z + unit k) then
          (f (z + unit k) - f z) ^ 2 else 0)
      ≤ ∑ z ∈ C, ∑ k : Fin 2, (if z ∈ C₀ then
          (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
            (f (z + unit k) - f z) ^ 2 else 0) else 0) :=
        Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun k _ => hterm z hz k
    _ = ∑ z ∈ C₀, ∑ k : Fin 2,
          (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
            (f (z + unit k) - f z) ^ 2 else 0) := by
        have e : ∀ z, ∑ k : Fin 2, (if z ∈ C₀ then
            (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
              (f (z + unit k) - f z) ^ 2 else 0) else 0) =
            if z ∈ C₀ then ∑ k : Fin 2,
              (if z + unit k ∈ C₀ ∧ (openGraph ω).Adj z (z + unit k) then
                (f (z + unit k) - f z) ^ 2 else 0) else 0 := fun z => by
          split_ifs <;> simp
        simp only [e]
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hC₀C]

/-- **Proposition 3.4 with `s = 2` for functions vanishing on the boundary, planar form.** There is
`K` such that, if all partition cubes of the vertices of the parent of a triadic cube `U` have
scale at most `k ≤ scale(U)` and `f` vanishes off the interior vertices of `C_*(U)`, then
`Σ_{C_*(U)} f² ≤ 4 (1 + (9/8) 9^k) K 9^{scale(U)+1} 81^k Σ_{open edges of C_*(U)} (∇f)²`. -/
theorem exists_planar_sum_sq_le_of_eq_zero :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration 2), PlanarPartitionEvent ω → ∀ (U : TriadicCube 2)
      (k : ℕ), k ≤ U.scale →
      (∀ x ∈ U.parent.vertices, (planarPartCube ω x).scale ≤ k) →
      ∀ f : Vertex 2 → ℝ,
      (∀ x, ¬(x ∈ clusterVertices ω U ∧ U.IsInterior x) → f x = 0) →
      ∑ x ∈ clusterVertices ω U, f x ^ 2 ≤
        4 * (1 + 9 / 8 * 9 ^ k) * K * 9 ^ (U.scale + 1) * 81 ^ k *
          ∑ z ∈ clusterVertices ω U, ∑ j : Fin 2,
            (if z + unit j ∈ clusterVertices ω U ∧ (openGraph ω).Adj z (z + unit j) then
              (f (z + unit j) - f z) ^ 2 else 0) := by
  obtain ⟨K, hK, hsob⟩ := exists_planar_sum_sq_le
  refine ⟨K, hK, fun ω hP U k hkm hk f hf => ?_⟩
  set m := U.scale
  set U' : TriadicCube 2 := U.parent
  have hUU' : U.vertices ⊆ U'.vertices := U.vertices_subset_parent
  have hU' : PlanarResolved ω U' := fun z hz => (hk z hz).trans (by change k ≤ U.scale + 1; omega)
  have hU : PlanarResolved ω U := fun z hz => (hk z (hUU' hz)).trans hkm
  set C := clusterVertices ω U'
  set C₀ := clusterVertices ω U
  have hC₀C : C₀ ⊆ C := clusterVertices_subset hUU'
  set E₀ := ∑ z ∈ C₀, ∑ j : Fin 2,
    (if z + unit j ∈ C₀ ∧ (openGraph ω).Adj z (z + unit j) then (f (z + unit j) - f z) ^ 2 else 0)
  have hE₀ : 0 ≤ E₀ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs <;> positivity
  -- `f` vanishes off `C₀`
  have hf0 : ∀ x, x ∉ C₀ → f x = 0 := fun x hx => hf x fun h => hx h.1
  -- the counting of `C \ C₀`
  have hcount := card_le_mul_card_sdiff_clusterVertices hP (U := U) (U' := U') hU' hkm hk
  have hcardU : U.toIntegerCube.vertices.card = 9 ^ m := by
    rw [IntegerCube.card_vertices]
    change (3 ^ U.scale) ^ 2 = 9 ^ U.scale
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hcardU' : U'.toIntegerCube.vertices.card = 9 ^ (m + 1) := by
    rw [IntegerCube.card_vertices]
    change (3 ^ (U.scale + 1)) ^ 2 = 9 ^ (U.scale + 1)
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hUU'f : U.toIntegerCube.vertices ⊆ U'.toIntegerCube.vertices := fun x hx => by
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx ⊢
    exact hUU' hx
  have hsd : (U'.toIntegerCube.vertices \ U.toIntegerCube.vertices).card = 8 * 9 ^ m := by
    rw [Finset.card_sdiff_of_subset hUU'f, hcardU, hcardU', pow_succ]
    omega
  rw [hsd] at hcount
  set D := C \ C₀
  have hD : (8 : ℝ) * 9 ^ m ≤ 9 ^ k * D.card := by exact_mod_cast hcount
  have hDpos : (0 : ℝ) < D.card := by
    have : (0 : ℝ) < 8 * 9 ^ m := by positivity
    have h9 : (0 : ℝ) < 9 ^ k := by positivity
    nlinarith
  have hCcard : (C.card : ℝ) ≤ 9 ^ (m + 1) := by
    have : C.card ≤ U'.toIntegerCube.vertices.card := Finset.card_le_card (Finset.filter_subset _ _)
    rw [hcardU'] at this
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C.card :=
    lt_of_lt_of_le hDpos (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset)
  -- the mean of `f` on `C`
  set fbar := (∑ x ∈ C, f x) / C.card
  set g : Vertex 2 → ℝ := fun y => f y - fbar
  have hg0 : ∑ x ∈ C, g x = 0 := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hCpos.ne']
    ring
  have hsobg := hsob ω hP U' hU' g hg0
  simp only [g, gradNormIn_sub_const] at hsobg
  -- the weights
  set W : Vertex 2 → ℝ := fun z => ((3 : ℝ) ^ (planarCoarseData hP U' hU').reachScale z) ^ 2 +
    (3 : ℝ) ^ (planarCoarseData hP U' hU').pairReachScale z
  have hW : ∀ z, W z ≤ 2 * 9 ^ k := by
    intro z
    obtain ⟨h1, h2⟩ := reachScale_le_of_forall hP hU' hk z
    have e1 : ((3 : ℝ) ^ (planarCoarseData hP U' hU').reachScale z) ^ 2 ≤ 9 ^ k := by
      rw [← pow_mul, show (9 : ℝ) ^ k = 3 ^ (2 * k) by rw [pow_mul]; norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have e2 : (3 : ℝ) ^ (planarCoarseData hP U' hU').pairReachScale z ≤ 9 ^ k := by
      rw [show (9 : ℝ) ^ k = 3 ^ (2 * k) by rw [pow_mul]; norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [W]
    linarith
  have hW0 : ∀ z, 0 ≤ W z := fun z => by simp only [W]; positivity
  -- Cauchy–Schwarz
  set G : Vertex 2 → ℝ := fun z => gradNormIn (openGraph ω) C f z
  have hcs : (∑ z ∈ C, W z * G z) ^ 2 ≤ (∑ z ∈ C, W z ^ 2) * ∑ z ∈ C, G z ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq C W G
  have hWsum : ∑ z ∈ C, W z ^ 2 ≤ 9 ^ (m + 1) * (4 * 81 ^ k) := by
    calc ∑ z ∈ C, W z ^ 2 ≤ ∑ _z ∈ C, (2 * 9 ^ k : ℝ) ^ 2 :=
          Finset.sum_le_sum fun z _ => pow_le_pow_left₀ (hW0 z) (hW z) 2
      _ = C.card * (4 * 81 ^ k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [show (2 * 9 ^ k : ℝ) ^ 2 = 4 * 81 ^ k by
            rw [mul_pow, ← pow_mul, show (81 : ℝ) ^ k = 9 ^ (2 * k) by rw [pow_mul]; norm_num]
            ring_nf]
      _ ≤ 9 ^ (m + 1) * (4 * 81 ^ k) := mul_le_mul_of_nonneg_right hCcard (by positivity)
  -- the gradient on the open edges
  have hG : ∑ z ∈ C, G z ^ 2 ≤ E₀ := by
    have h1 : ∑ z ∈ C, G z ^ 2 = (1 / 2) * ∑ z ∈ C, ∑ y ∈ C,
        (if (openGraph ω).Adj z y then (f z - f y) ^ 2 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [G, gradNormIn]
      rw [Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => by
        split_ifs <;> positivity))]
    rw [h1, sum_sum_openAdj_eq_two_mul C (fun z y => (f z - f y) ^ 2) (fun z y => by ring)]
    have e : ∀ z j, (if z + unit j ∈ C ∧ (openGraph ω).Adj z (z + unit j) then
        (f z - f (z + unit j)) ^ 2 else 0) =
        (if z + unit j ∈ C ∧ (openGraph ω).Adj z (z + unit j) then
          (f (z + unit j) - f z) ^ 2 else 0) := fun z j => by split_ifs <;> ring
    simp only [e]
    have := sum_edges_le_of_support hP hUU' hU f hf
    linarith
  -- the mean
  have hmean : (C.card : ℝ) * fbar ^ 2 ≤ C.card / D.card * ∑ x ∈ C, g x ^ 2 := by
    have hDsum : ∑ x ∈ D, g x ^ 2 = D.card * fbar ^ 2 := by
      rw [Finset.sum_congr rfl fun x hx => by
        rw [show g x = -fbar by simp only [g, hf0 x (Finset.mem_sdiff.1 hx).2, zero_sub]]]
      rw [Finset.sum_const, nsmul_eq_mul, neg_sq]
    have hDle : ∑ x ∈ D, g x ^ 2 ≤ ∑ x ∈ C, g x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => sq_nonneg _
    rw [hDsum] at hDle
    rw [div_mul_eq_mul_div, le_div_iff₀ hDpos]
    nlinarith
  have hsplit : ∑ x ∈ C, f x ^ 2 = ∑ x ∈ C, g x ^ 2 + C.card * fbar ^ 2 := by
    have : ∀ x, f x ^ 2 = g x ^ 2 + 2 * fbar * g x + fbar ^ 2 := fun x => by simp only [g]; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hg0, Finset.sum_const,
      nsmul_eq_mul]
    ring
  have hratio : (C.card : ℝ) / D.card ≤ 9 / 8 * 9 ^ k := by
    rw [div_le_iff₀ hDpos]
    have : (9 : ℝ) ^ (m + 1) = 9 * 9 ^ m := by rw [pow_succ]; ring
    nlinarith
  have hg2 : ∑ x ∈ C, g x ^ 2 ≤ K * ((∑ z ∈ C, W z ^ 2) * ∑ z ∈ C, G z ^ 2) :=
    hsobg.trans (mul_le_mul_of_nonneg_left hcs hK)
  have hgg : 0 ≤ ∑ x ∈ C, g x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ x ∈ C₀, f x ^ 2 ≤ ∑ x ∈ C, f x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hC₀C fun _ _ _ => sq_nonneg _
    _ ≤ (1 + 9 / 8 * 9 ^ k) * ∑ x ∈ C, g x ^ 2 := by
        rw [hsplit]
        nlinarith
    _ ≤ (1 + 9 / 8 * 9 ^ k) * (K * ((9 ^ (m + 1) * (4 * 81 ^ k)) * E₀)) := by
        refine mul_le_mul_of_nonneg_left (hg2.trans ?_) (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact mul_le_mul hWsum hG (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = 4 * (1 + 9 / 8 * 9 ^ k) * K * 9 ^ (m + 1) * 81 ^ k * E₀ := by ring

end Rigidity.Dirichlet
