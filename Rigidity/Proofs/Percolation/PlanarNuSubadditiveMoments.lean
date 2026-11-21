import Rigidity.Proofs.Percolation.PlanarNuSubadditive
import Rigidity.Proofs.Percolation.PlanarMuSubadditiveMoments

/-!
# Expected error in the subadditivity of `ν`

A vertex `x` is *exceptional* at scale `n` when its subcube `V(x)` of scale `n` is unresolved or
the square of side `9 s_x` around its partition cube leaves `V(x)`. At a vertex of `C_*(U)` which
is not exceptional, every open edge lies in `C_*(V(x))`: the local path from `x` to the anchor of
its partition cube stays in the window, which lies in the square of side `9 s_x`. So the flux
error in the subadditivity of `ν` is carried by the open edges at exceptional vertices, and by
the Cauchy–Schwarz and Young inequalities it is at most
`(9 / 4) |p|₁² (3 ^ (n / 2) G + |U| / 3 ^ (n / 2))`, where `G` is the number of exceptional
vertices of `U`.

If `V(x)` is resolved and `x` is exceptional, the square of side `9 s_x` contains a boundary vertex
of `V(x)`. By the overlap bound for these squares and the moments of the reach,
`E[G] ≤ C |U| / 3 ^ n`, and so

`E[(|U| ν(U, p) - ∑_{x ∈ U} 1{V(x) resolved} ν(V(x), p))⁺] ≤ C |p|₁² |U| / 3 ^ (n / 2)`

uniformly in `U` and `n` (Armstrong and Dario, Lemma 4.8, (4.18), in expectation; the set `W` of
the proof there is the set of exceptional vertices).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- A vertex is exceptional at scale `n` when its subcube of scale `n` is unresolved or the square
of side `9s` around its partition cube leaves the subcube. -/
def SubcubeExceptional (ω : Configuration 2) (n : ℕ) (x : Vertex 2) : Prop :=
  ¬ (PlanarResolved ω (scaleCube n x) ∧
    (↑(planarPartCube ω x).ninefold.vertices : Set (Vertex 2)) ⊆ (scaleCube n x).vertices)

/-- Lattice neighbours of a vertex of a triadic cube lie in the square of side `9s` around it. -/
theorem mem_ninefold_of_near {Q : TriadicCube 2} {x y : Vertex 2} (hx : x ∈ Q.vertices)
    (hxy : ∀ i, |y i - x i| ≤ 1) : y ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) := by
  rw [TriadicCube.mem_ninefold]
  intro i
  have h1 := Q.abs_sub_center_le hx i
  have h2 := Q.two_mul_ninefoldRadius
  have h3 := hxy i
  have h4 : |y i - Q.center i| ≤ |y i - x i| + |x i - Q.center i| := abs_sub_le _ _ _
  have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  linarith

/-- A box meeting a cube and its complement contains a vertex of a face of the cube. -/
theorem exists_face_mem_of_mem_of_not_mem {A B : IntegerCube 2} {x w : Vertex 2}
    (hxA : x ∈ A.vertices) (hxB : x ∈ B.vertices) (hwB : w ∈ B.vertices)
    (hwA : w ∉ A.vertices) :
    ∃ i : Fin 2, ∃ b ∈ B.vertices, b ∈ A.lowerFace i ∨ b ∈ A.upperFace i := by
  rw [IntegerCube.mem_vertices] at hxA hxB hwB hwA
  push Not at hwA
  obtain ⟨i, hi⟩ := hwA
  set b : Vertex 2 := fun j => if w j < A.corner j then A.corner j else
    if A.corner j + (A.size : ℤ) ≤ w j then A.corner j + (A.size : ℤ) - 1 else w j with hb
  have hbA : ∀ j, A.corner j ≤ b j ∧ b j < A.corner j + (A.size : ℤ) := by
    intro j
    obtain ⟨h1, h2⟩ := hxA j
    simp only [hb]
    split_ifs <;> omega
  have hbB : ∀ j, B.corner j ≤ b j ∧ b j < B.corner j + (B.size : ℤ) := by
    intro j
    obtain ⟨h1, h2⟩ := hxA j
    obtain ⟨h3, h4⟩ := hxB j
    obtain ⟨h5, h6⟩ := hwB j
    simp only [hb]
    split_ifs <;> omega
  have hbAv : b ∈ A.vertices := (IntegerCube.mem_vertices _ _).2 hbA
  refine ⟨i, b, (IntegerCube.mem_vertices _ _).2 hbB, ?_⟩
  by_cases hlt : w i < A.corner i
  · left
    rw [IntegerCube.mem_lowerFace]
    refine ⟨hbAv, ?_⟩
    simp only [hb, if_pos hlt]
  · right
    rw [IntegerCube.mem_upperFace]
    refine ⟨hbAv, ?_⟩
    have hge : A.corner i + (A.size : ℤ) ≤ w i := hi (not_lt.1 hlt)
    simp only [hb, if_neg hlt, if_pos hge]
    omega

/-- A vertex of the cluster of a resolved cube whose partition cube has its square of side `9s`
inside a triadic cube `V` belongs to the cluster of `V`. -/
theorem mem_planarCubeCluster_of_ninefold_subset (hP : PlanarPartitionEvent ω)
    {U V : TriadicCube 2} (hU : PlanarResolved ω U) {x : Vertex 2}
    (hx : x ∈ planarCubeCluster ω U) (hxV : x ∈ V.vertices)
    (h9 : (↑(planarPartCube ω x).ninefold.vertices : Set (Vertex 2)) ⊆ V.vertices) :
    x ∈ planarCubeCluster ω V := by
  have hsub := planarPartCube_subset_of_resolved hP hU hx.1
  have hw := (planarPartCube ω x).reachIn_window_of_reachIn (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x) (hU x hx.1) hsub (planarPartCube_spec hP x).1 hx.2
  have hwV : (↑((planarPartCube ω x).window U).vertices : Set (Vertex 2)) ⊆ V.vertices :=
    fun z hz => h9 (Finset.mem_coe.2 (TriadicCube.subset_ninefold_of_mem_planarSquares
      ((planarPartCube ω x).window_mem_planarSquares (hU x hx.1) hsub) (Finset.mem_coe.1 hz)))
  exact ⟨hxV, (hw.mono hwV).symm⟩

/-- **Open edges at non-exceptional vertices.** An open edge of the cluster of a resolved cube at a
vertex which is not exceptional lies in the cluster of the subcube of the vertex. -/
theorem isSubcubePair_of_not_exceptional (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} {x y : Vertex 2} (hx : x ∈ planarCubeCluster ω U)
    (hxy : (openGraph ω).Adj x y) (hex : ¬ SubcubeExceptional ω n x) :
    IsSubcubePair ω n x y := by
  unfold SubcubeExceptional at hex
  rw [not_not] at hex
  obtain ⟨hres, h9⟩ := hex
  have hxV : x ∈ (scaleCube n x).vertices := mem_scaleCube n x
  have hxC := mem_planarCubeCluster_of_ninefold_subset hP hU hx hxV h9
  have hyV : y ∈ (scaleCube n x).vertices :=
    h9 (mem_ninefold_of_near (planarPartCube_spec hP x).1
      fun i => Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hxy) i)
  have hyx : ReachIn ω (scaleCube n x).vertices y x :=
    ⟨SimpleGraph.Walk.cons hxy.symm SimpleGraph.Walk.nil, fun w hw => by
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hyV
      · exact hxV⟩
  exact ⟨hres, mem_clusterVertices.2 hxC,
    mem_clusterVertices.2 (mem_planarCubeCluster_of_reachIn hP hres hyV hxV (hyx.trans hxC.2))⟩

/-- The indicator of the exceptional vertices. -/
noncomputable def exceptionalIndicator (ω : Configuration 2) (n : ℕ) (x : Vertex 2) : ℝ :=
  if SubcubeExceptional ω n x then 1 else 0

theorem exceptionalIndicator_nonneg (n : ℕ) (x : Vertex 2) : 0 ≤ exceptionalIndicator ω n x := by
  unfold exceptionalIndicator
  split_ifs <;> norm_num

/-- **Young's bound for the flux error.** -/
theorem nuError_le_young (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (p : Fin 2 → ℝ) (v : ClusterFun ω U) {t : ℝ}
    (ht : 0 < t) :
    (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
        (if IsSubcubePair ω n x y then 0 else fluxTerm ω U p v x y) ≤
      (|p 0| + |p 1|) * (9 * (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) / t +
        t * (2 * clusterForm ω U v v)) / 4 := by
  set g : ↥(clusterVertices ω U) → ℝ := fun x => exceptionalIndicator ω n x.1 with hg
  have hP1 : 0 ≤ |p 0| + |p 1| := by positivity
  have hg0 : ∀ x, 0 ≤ g x := fun x => exceptionalIndicator_nonneg n x.1
  have hX0 : 0 ≤ ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then |v x - v y| else 0) * g x :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (by split_ifs <;> positivity) (hg0 x)
  have hT0 : 0 ≤ ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then g x ^ 2 else 0) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
  have hB0 : 0 ≤ 2 * clusterForm ω U v v := by
    have := clusterForm_self_nonneg v
    linarith
  have hCS := sum_adj_abs_mul_sq_le v g
  have hT9 := sum_adj_le_nine_mul (fun x => g x ^ 2) fun _ => sq_nonneg _
  have hgsq : ∑ x, g x ^ 2 ≤ ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x := by
    calc ∑ x, g x ^ 2 = ∑ x : ↥(clusterVertices ω U), exceptionalIndicator ω n x.1 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hg, exceptionalIndicator]
          split_ifs <;> norm_num
      _ = ∑ x ∈ clusterVertices ω U, exceptionalIndicator ω n x :=
          Finset.sum_coe_sort (clusterVertices ω U) (exceptionalIndicator ω n)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun x _ _ => exceptionalIndicator_nonneg n x
  have hXle := le_of_sq_le_mul hX0 hT0 hB0 ht hCS
  have hpt : ∀ x y : ↥(clusterVertices ω U),
      (if IsSubcubePair ω n x.1 y.1 then 0 else fluxTerm ω U p v x.1 y.1) ≤
        (|p 0| + |p 1|) * ((if (openGraph ω).Adj x.1 y.1 then |v x - v y| else 0) * g x) := by
    intro x y
    by_cases hadj : (openGraph ω).Adj x.1 y.1
    · by_cases hpair : IsSubcubePair ω n x.1 y.1
      · rw [if_pos hpair, if_pos hadj]
        exact mul_nonneg hP1 (mul_nonneg (abs_nonneg _) (hg0 x))
      · rw [if_neg hpair, if_pos hadj]
        have hex : SubcubeExceptional ω n x.1 := by
          by_contra hne
          exact hpair (isSubcubePair_of_not_exceptional hP hU (mem_clusterVertices.1 x.2)
            hadj hne)
        have hgx : g x = 1 := by simp only [hg, exceptionalIndicator, if_pos hex]
        rw [hgx, mul_one]
        unfold fluxTerm
        rw [if_pos hadj, clusterExtend_apply_of_mem v y.2, clusterExtend_apply_of_mem v x.2]
        have hcoord : ∀ i, |((y.1 i : ℤ) : ℝ) - ((x.1 i : ℤ) : ℝ)| ≤ 1 := fun i => by
          have := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hadj) i
          exact_mod_cast this
        have hp : |∑ i, p i * (((y.1 i : ℤ) : ℝ) - ((x.1 i : ℤ) : ℝ))| ≤ |p 0| + |p 1| := by
          rw [Fin.sum_univ_two]
          calc _ ≤ |p 0 * (((y.1 0 : ℤ) : ℝ) - ((x.1 0 : ℤ) : ℝ))| +
                |p 1 * (((y.1 1 : ℤ) : ℝ) - ((x.1 1 : ℤ) : ℝ))| := abs_add_le _ _
            _ ≤ |p 0| * 1 + |p 1| * 1 := by
                rw [abs_mul, abs_mul]
                exact add_le_add (mul_le_mul_of_nonneg_left (hcoord 0) (abs_nonneg _))
                  (mul_le_mul_of_nonneg_left (hcoord 1) (abs_nonneg _))
            _ = _ := by ring
        calc (∑ i, p i * (((y.1 i : ℤ) : ℝ) - ((x.1 i : ℤ) : ℝ))) * (v y - v x)
            ≤ |∑ i, p i * (((y.1 i : ℤ) : ℝ) - ((x.1 i : ℤ) : ℝ))| * |v y - v x| := by
              rw [← abs_mul]
              exact le_abs_self _
          _ ≤ (|p 0| + |p 1|) * |v x - v y| := by
              rw [abs_sub_comm (v y) (v x)]
              exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    · rw [if_neg hadj, zero_mul, mul_zero]
      split_ifs
      · exact le_rfl
      · simp [fluxTerm, hadj]
  have hsum : ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
      (if IsSubcubePair ω n x y then 0 else fluxTerm ω U p v x y) ≤
      (|p 0| + |p 1|) * ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then |v x - v y| else 0) * g x := by
    rw [← Finset.sum_coe_sort (clusterVertices ω U), Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_coe_sort (clusterVertices ω U), Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => hpt x y
  set G := ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x with hG
  set X := ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    (if (openGraph ω).Adj x.1 y.1 then |v x - v y| else 0) * g x with hX
  set T := ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    (if (openGraph ω).Adj x.1 y.1 then g x ^ 2 else 0) with hT
  have hT' : T / t ≤ 9 * G / t := div_le_div_of_nonneg_right (by linarith) ht.le
  have h3 : (T / t + t * (2 * clusterForm ω U v v)) / 2 ≤
      (9 * G / t + t * (2 * clusterForm ω U v v)) / 2 := by linarith
  have h4 := mul_le_mul_of_nonneg_left (hXle.trans h3) hP1
  calc (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
        (if IsSubcubePair ω n x y then 0 else fluxTerm ω U p v x y)
      ≤ (1 / 2 : ℝ) * ((|p 0| + |p 1|) * ((9 * G / t + t * (2 * clusterForm ω U v v)) / 2)) := by
        linarith
    _ = _ := by ring

/-- **Subadditivity of `ν` with a quantified error.** -/
theorem planarNu_mul_volume_le_young (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (p : Fin 2 → ℝ) {t : ℝ} (ht : 0 < t) :
    planarNu ω U p * U.volume ≤
      ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) p else 0) +
        (|p 0| + |p 1|) * (9 * (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) / t +
          t * (9 * (|p 0| + |p 1|) ^ 2 * U.volume)) / 4 := by
  obtain ⟨v, hv, hvar, hsub⟩ := planarNu_le_sum_subcubes hP hn p
  obtain ⟨v', hv', hvar', hν'⟩ := exists_planarNu_maximizer (ω := ω) (U := U) p
  have hBeq : clusterForm ω U v v = clusterForm ω U v' v' := by
    have h1 := hvar v' hv'
    have h2 := hvar' v hv
    have h3 := hvar v hv
    have h4 := hvar' v' hv'
    rw [clusterForm_symm] at h1
    linarith
  have hvol := U.volume_pos
  have hνB : planarNu ω U p * U.volume = clusterForm ω U v' v' / 2 := by
    rw [hν', div_mul_cancel₀ _ hvol.ne', ← hvar' v' hv']
    ring
  have hνle := planarNu_le (ω := ω) (U := U) p
  have hB : 2 * clusterForm ω U v v ≤ 9 * (|p 0| + |p 1|) ^ 2 * U.volume := by
    rw [hBeq]
    have := mul_le_mul_of_nonneg_right hνle hvol.le
    linarith
  have herr := nuError_le_young hP hU (n := n) p v ht
  set G := ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x with hG
  have hP1 : 0 ≤ |p 0| + |p 1| := by positivity
  have h1 := mul_le_mul_of_nonneg_left hB ht.le
  have h2 := mul_le_mul_of_nonneg_left (add_le_add (le_refl (9 * G / t)) h1) hP1
  linarith

/-- An exceptional vertex of a resolved subcube has a boundary vertex of the subcube in the square
of side `9s` around its partition cube. -/
theorem exceptionalIndicator_le (hP : PlanarPartitionEvent ω) (n : ℕ) (x : Vertex 2) :
    exceptionalIndicator ω n x ≤
      (if PlanarResolved ω (scaleCube n x) then 0 else 1) +
        ∑ k ∈ boundaryIndex (scaleCube n x),
          (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) := by
  have hS : 0 ≤ ∑ k ∈ boundaryIndex (scaleCube n x),
      (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num
  unfold exceptionalIndicator
  by_cases hex : SubcubeExceptional ω n x
  · rw [if_pos hex]
    by_cases hres : PlanarResolved ω (scaleCube n x)
    · rw [if_pos hres, zero_add]
      have h9 : ¬ (↑(planarPartCube ω x).ninefold.vertices : Set (Vertex 2)) ⊆
          (scaleCube n x).vertices := fun h => hex ⟨hres, h⟩
      rw [Set.not_subset] at h9
      obtain ⟨w, hw9, hwV⟩ := h9
      have hx9 : x ∈ (planarPartCube ω x).ninefold.vertices :=
        Finset.mem_coe.1 (mem_ninefold_of_near (planarPartCube_spec hP x).1 fun i => by simp)
      have hxV : x ∈ (scaleCube n x).toIntegerCube.vertices :=
        ((scaleCube n x).mem_toIntegerCube_vertices x).2 (mem_scaleCube n x)
      have hwV' : w ∉ (scaleCube n x).toIntegerCube.vertices := fun h =>
        hwV (((scaleCube n x).mem_toIntegerCube_vertices w).1 h)
      obtain ⟨i, b, hb9, hbf⟩ :=
        exists_face_mem_of_mem_of_not_mem hxV hx9 (Finset.mem_coe.1 hw9) hwV'
      have hk : ∃ k ∈ boundaryIndex (scaleCube n x), k.2.2 = b := by
        rcases hbf with hbl | hbu
        · refine ⟨(i, false, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_univ _,
            Finset.mem_product.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hbl).1⟩⟩, ?_⟩, rfl⟩
          simpa using hbl
        · refine ⟨(i, true, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_univ _,
            Finset.mem_product.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hbu).1⟩⟩, ?_⟩, rfl⟩
          simpa using hbu
      obtain ⟨k, hkB, rfl⟩ := hk
      calc (1 : ℝ) = if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then 1 else 0 := by
            rw [if_pos hb9]
        _ ≤ _ := Finset.single_le_sum (f := fun k : Fin 2 × Bool × Vertex 2 =>
            if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0)
            (fun k _ => by split_ifs <;> norm_num) hkB
    · rw [if_neg hres]
      linarith
  · rw [if_neg hex]
    have : (0 : ℝ) ≤ if PlanarResolved ω (scaleCube n x) then 0 else 1 := by
      split_ifs <;> norm_num
    linarith

/-- The reach-sum majorant of the number of exceptional vertices. -/
noncomputable def exceptionalCountBound (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) :
    ℝ≥0∞ :=
  ∑ x ∈ U.toIntegerCube.vertices, ∑ z ∈ (scaleCube n x).toIntegerCube.vertices,
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * reachSum ω 6 z +
    ∑ V ∈ subcubesAt U n, ∑ k ∈ boundaryIndex V, 121 * reachSum ω 2 k.2.2

theorem measurable_exceptionalCountBound (U : TriadicCube 2) (n : ℕ) :
    Measurable fun ω : Configuration 2 => exceptionalCountBound ω U n := by
  unfold exceptionalCountBound
  exact (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun z _ =>
      (measurable_reachSum 6 z).const_mul _).add
    (Finset.measurable_sum _ fun V _ => Finset.measurable_sum _ fun k _ =>
      (measurable_reachSum 2 k.2.2).const_mul _)

/-- On the partition event the number of exceptional vertices is bounded by its majorant. -/
theorem ofReal_sum_exceptionalIndicator_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    {n : ℕ} (hn : n ≤ U.scale) :
    ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) ≤
      exceptionalCountBound ω U n := by
  have hnn1 : ∀ z : Vertex 2, 0 ≤ (partSide ω z / 3 ^ (n + 1)) ^ 6 := fun z => by positivity
  have hnn2 : ∀ (V : TriadicCube 2) (k : Fin 2 × Bool × Vertex 2), 0 ≤
      ∑ x ∈ V.toIntegerCube.vertices,
        (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) :=
    fun V k => Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num
  have hre : ∑ x ∈ U.toIntegerCube.vertices, ∑ k ∈ boundaryIndex (scaleCube n x),
      (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) =
      ∑ V ∈ subcubesAt U n, ∑ k ∈ boundaryIndex V, ∑ x ∈ V.toIntegerCube.vertices,
        (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) := by
    rw [sum_scaleCube_eq hn (fun V x => ∑ k ∈ boundaryIndex V,
      (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0))]
    exact Finset.sum_congr rfl fun V _ => Finset.sum_comm
  have h1 : ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x ≤
      ∑ x ∈ U.toIntegerCube.vertices, ∑ z ∈ (scaleCube n x).toIntegerCube.vertices,
        (partSide ω z / 3 ^ (n + 1)) ^ 6 +
      ∑ V ∈ subcubesAt U n, ∑ k ∈ boundaryIndex V, ∑ x ∈ V.toIntegerCube.vertices,
        (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) := by
    rw [← hre, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => (exceptionalIndicator_le hP n x).trans
      (add_le_add (indicator_unresolved_le (ω := ω) (n := n) x) le_rfl)
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ENNReal.ofReal_add (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun z _ => hnn1 z)
    (Finset.sum_nonneg fun V _ => Finset.sum_nonneg fun k _ => hnn2 V k)]
  unfold exceptionalCountBound
  refine add_le_add ?_ ?_
  · rw [ENNReal.ofReal_sum_of_nonneg fun x _ => Finset.sum_nonneg fun z _ => hnn1 z]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun z _ => hnn1 z]
    refine Finset.sum_le_sum fun z _ => ?_
    have e : (partSide ω z / 3 ^ (n + 1)) ^ 6 =
        1 / (3 : ℝ) ^ (6 * (n + 1)) * partSide ω z ^ (5 + 1) := by
      rw [div_pow, ← pow_mul, mul_comm (n + 1) 6]
      ring
    rw [e, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_of_nonneg_left (ofReal_partSide_pow_le hP z 5) zero_le
  · rw [ENNReal.ofReal_sum_of_nonneg fun V _ => Finset.sum_nonneg fun k _ => hnn2 V k]
    refine Finset.sum_le_sum fun V _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => hnn2 V k]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := ofReal_sum_ninefold_le hP V.toIntegerCube.vertices k.2.2 0
    simp only [zero_mul, pow_zero, zero_add] at h
    have h2 : planarReach ω k.2.2 ^ 2 ≤ reachSum ω 2 k.2.2 := planarReach_pow_le ω k.2.2 1
    exact h.trans (mul_le_mul_of_nonneg_left h2 zero_le)

/-- The expected majorant of the number of exceptional vertices. -/
theorem lintegral_exceptionalCountBound_le {p : unitInterval} {C₂ C₆ : ℝ≥0∞}
    (h2 : ∀ a, ∫⁻ ω, reachSum ω 2 a ∂(latticeBondLaw 2 p) ≤ C₂)
    (h6 : ∀ a, ∫⁻ ω, reachSum ω 6 a ∂(latticeBondLaw 2 p) ≤ C₆) (U : TriadicCube 2) {n : ℕ} :
    ∫⁻ ω, exceptionalCountBound ω U n ∂(latticeBondLaw 2 p) ≤
      (U.toIntegerCube.vertices.card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
        (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * C₆)) +
      ((subcubesAt U n).card : ℝ≥0∞) * (ENNReal.ofReal (4 * (3 : ℝ) ^ n) * (121 * C₂)) := by
  have hm1 : ∀ z : Vertex 2, Measurable fun ω : Configuration 2 =>
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * reachSum ω 6 z :=
    fun z => (measurable_reachSum 6 z).const_mul _
  have hm2 : ∀ k : Fin 2 × Bool × Vertex 2, Measurable fun ω : Configuration 2 =>
      121 * reachSum ω 2 k.2.2 :=
    fun k => (measurable_reachSum 2 k.2.2).const_mul _
  unfold exceptionalCountBound
  rw [lintegral_add_left (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _
      fun z _ => hm1 z),
    lintegral_finsetSum _ fun x _ => Finset.measurable_sum _ fun z _ => hm1 z,
    lintegral_finsetSum _ fun V _ => Finset.measurable_sum _ fun k _ => hm2 k]
  refine add_le_add ?_ ?_
  · calc ∑ x ∈ U.toIntegerCube.vertices, ∫⁻ ω, ∑ z ∈ (scaleCube n x).toIntegerCube.vertices,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * reachSum ω 6 z ∂(latticeBondLaw 2 p)
        ≤ ∑ _x ∈ U.toIntegerCube.vertices, ENNReal.ofReal ((9 : ℝ) ^ n) *
          (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * C₆) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [lintegral_finsetSum _ fun z _ => hm1 z]
          calc ∑ z ∈ (scaleCube n x).toIntegerCube.vertices, ∫⁻ ω,
                ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * reachSum ω 6 z
                  ∂(latticeBondLaw 2 p)
              ≤ ∑ _z ∈ (scaleCube n x).toIntegerCube.vertices,
                ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * C₆ := by
                refine Finset.sum_le_sum fun z _ => ?_
                rw [lintegral_const_mul _ (measurable_reachSum 6 z)]
                exact mul_le_mul_of_nonneg_left (h6 z) zero_le
            _ = _ := by
                rw [Finset.sum_const, nsmul_eq_mul, card_toIntegerCube_vertices,
                  TriadicCube.volume, scale_scaleCube]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  · calc ∑ V ∈ subcubesAt U n, ∫⁻ ω, ∑ k ∈ boundaryIndex V, 121 * reachSum ω 2 k.2.2
          ∂(latticeBondLaw 2 p)
        ≤ ∑ _V ∈ subcubesAt U n, ENNReal.ofReal (4 * (3 : ℝ) ^ n) * (121 * C₂) := by
          refine Finset.sum_le_sum fun V hV => ?_
          rw [lintegral_finsetSum _ fun k _ => hm2 k]
          calc ∑ k ∈ boundaryIndex V, ∫⁻ ω, 121 * reachSum ω 2 k.2.2 ∂(latticeBondLaw 2 p)
              ≤ ∑ _k ∈ boundaryIndex V, 121 * C₂ := by
                refine Finset.sum_le_sum fun k _ => ?_
                rw [lintegral_const_mul _ (measurable_reachSum 2 k.2.2)]
                exact mul_le_mul_of_nonneg_left (h2 k.2.2) zero_le
            _ = ((boundaryIndex V).card : ℝ≥0∞) * (121 * C₂) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ _ := by
                have hc := card_boundaryIndex_le V
                have hs : (V.toIntegerCube.size : ℝ) = (3 : ℝ) ^ n := by
                  change ((3 ^ V.scale : ℕ) : ℝ) = _
                  rw [scale_of_mem_subcubesAt hV]
                  push_cast
                  rfl
                rw [hs] at hc
                have hcard : ((boundaryIndex V).card : ℝ≥0∞) ≤
                    ENNReal.ofReal (4 * (3 : ℝ) ^ n) := by
                  rw [← ENNReal.ofReal_natCast]
                  exact ENNReal.ofReal_le_ofReal hc
                exact mul_le_mul_of_nonneg_right hcard zero_le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Expected error in the subadditivity of `ν`** (Armstrong and Dario, Lemma 4.8, (4.18), in
expectation). -/
theorem exists_lintegral_planarNu_sub_sum_subcubes_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ ξ : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
              (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0))
          else 0) ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 * U.volume / Real.sqrt (3 ^ n)) := by
  obtain ⟨C₂, hC₂, h2⟩ := exists_lintegral_tsum_ninefold_le hpc 2
  obtain ⟨C₆, hC₆, h6⟩ := exists_lintegral_tsum_ninefold_le hpc 6
  refine ⟨3 * C₆ + 9 * (121 * C₂) + 3, by finiteness, fun U n hn ξ => ?_⟩
  have h2' : ∀ a, ∫⁻ ω, reachSum ω 2 a ∂(latticeBondLaw 2 p) ≤ C₂ := h2
  have h6' : ∀ a, ∫⁻ ω, reachSum ω 6 a ∂(latticeBondLaw 2 p) ≤ C₆ := h6
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 3 ^ n := Real.sq_sqrt (by positivity)
  have hvol := U.volume_pos
  have hP0 : 0 ≤ P₁ := by positivity
  set A := ENNReal.ofReal (9 / 4 * P₁ ^ 2 * s) with hA
  set a := ENNReal.ofReal (P₁ ^ 2 * U.volume / s) with ha
  have hpoint : ∀ ω : Configuration 2, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0))
      else 0) ≤
      A * exceptionalCountBound ω U n + ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) := by
    intro ω
    split_ifs with h
    · have hG0 : 0 ≤ ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x :=
        Finset.sum_nonneg fun x _ => exceptionalIndicator_nonneg n x
      have hb : planarNu ω U ξ * U.volume - ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) ≤
          9 / 4 * P₁ ^ 2 * s * (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) +
            9 / 4 * (P₁ ^ 2 * U.volume / s) := by
        rcases hP0.eq_or_lt with hz | hpos
        · have hy := planarNu_mul_volume_le_young h.1 h.2 hn ξ (t := 1) one_pos
          rw [← hP₁, ← hz] at hy
          rw [← hz]
          have : (0 : ℝ) ≤ 9 / 4 * 0 ^ 2 * s *
              (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) +
              9 / 4 * (0 ^ 2 * U.volume / s) := by
            simp
          simp only [zero_mul, zero_div, add_zero] at hy
          linarith
        · have ht : 0 < 1 / (P₁ * s) := by positivity
          have hy := planarNu_mul_volume_le_young h.1 h.2 hn ξ ht
          rw [← hP₁] at hy
          have e : P₁ * (9 * (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) /
              (1 / (P₁ * s)) + 1 / (P₁ * s) * (9 * P₁ ^ 2 * U.volume)) / 4 =
              9 / 4 * P₁ ^ 2 * s *
                (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) +
              9 / 4 * (P₁ ^ 2 * U.volume / s) := by
            field_simp
          rw [e] at hy
          linarith
      refine (ENNReal.ofReal_le_ofReal hb).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
      exact add_le_add (mul_le_mul_of_nonneg_left (ofReal_sum_exceptionalIndicator_le h.1 hn)
        zero_le) le_rfl
    · exact zero_le
  have hX := lintegral_exceptionalCountBound_le h2' h6' U (n := n)
  have hcardU : (U.toIntegerCube.vertices.card : ℝ≥0∞) = ENNReal.ofReal U.volume :=
    card_toIntegerCube_vertices U
  have hsub : ((subcubesAt U n).card : ℝ) * (9 : ℝ) ^ n = U.volume := card_subcubesAt_mul hn
  have k1 : A * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))))) ≤ 3 * a := by
    rw [hcardU, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hA,
      ← ENNReal.ofReal_mul (by positivity), ha, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (3 : ℝ) * (P₁ ^ 2 * U.volume / s) = 3 * P₁ ^ 2 * U.volume / s by ring,
      le_div_iff₀ hspos]
    have h27 : (3 : ℝ) ^ n * 9 ^ n ≤ 3 ^ (6 * (n + 1)) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hr : s ^ 2 * 9 ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1))) ≤ 1 := by
      rw [hs2, mul_one_div, div_le_one (by positivity)]
      exact h27
    have e : 9 / 4 * P₁ ^ 2 * s * (U.volume * ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1))))) * s =
        9 / 4 * (P₁ ^ 2 * U.volume) * (s ^ 2 * 9 ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)))) := by ring
    rw [e]
    have hc0 : (0 : ℝ) ≤ 9 / 4 * (P₁ ^ 2 * U.volume) := by positivity
    have := mul_le_mul_of_nonneg_left hr hc0
    nlinarith
  have k2 : A * (((subcubesAt U n).card : ℝ≥0∞) * ENNReal.ofReal (4 * (3 : ℝ) ^ n)) ≤ 9 * a := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hA,
      ← ENNReal.ofReal_mul (by positivity), ha, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (9 : ℝ) * (P₁ ^ 2 * U.volume / s) = 9 * P₁ ^ 2 * U.volume / s by ring,
      le_div_iff₀ hspos]
    have h9 : (9 : ℝ) ^ n = 3 ^ n * 3 ^ n := by rw [← mul_pow]; norm_num
    have e : 9 / 4 * P₁ ^ 2 * s * (((subcubesAt U n).card : ℝ) * (4 * (3 : ℝ) ^ n)) * s =
        9 * P₁ ^ 2 * (((subcubesAt U n).card : ℝ) * (9 : ℝ) ^ n) := by
      calc 9 / 4 * P₁ ^ 2 * s * (((subcubesAt U n).card : ℝ) * (4 * (3 : ℝ) ^ n)) * s
          = 9 * P₁ ^ 2 * ((subcubesAt U n).card : ℝ) * 3 ^ n * s ^ 2 := by ring
        _ = 9 * P₁ ^ 2 * ((subcubesAt U n).card : ℝ) * 3 ^ n * 3 ^ n := by rw [hs2]
        _ = _ := by rw [h9]; ring
    exact (e.trans (by rw [hsub])).le
  have k3 : ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) ≤ 3 * a := by
    rw [ha, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ P₁ ^ 2 * U.volume / s := by positivity
    linarith
  refine (lintegral_mono hpoint).trans ?_
  calc ∫⁻ ω, (A * exceptionalCountBound ω U n +
        ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s))) ∂(latticeBondLaw 2 p)
      = A * ∫⁻ ω, exceptionalCountBound ω U n ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul A (measurable_exceptionalCountBound U n), lintegral_const,
          measure_univ, mul_one]
    _ ≤ A * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
          (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * C₆)) +
        ((subcubesAt U n).card : ℝ≥0∞) * (ENNReal.ofReal (4 * (3 : ℝ) ^ n) * (121 * C₂))) +
          ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) := by gcongr
    _ = (A * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1)))))) * C₆ +
        (A * (((subcubesAt U n).card : ℝ≥0∞) * ENNReal.ofReal (4 * (3 : ℝ) ^ n))) *
          (121 * C₂) + ENNReal.ofReal (9 / 4 * (P₁ ^ 2 * U.volume / s)) := by ring
    _ ≤ (3 * a) * C₆ + (9 * a) * (121 * C₂) + 3 * a := by gcongr
    _ = _ := by ring

end Rigidity.Percolation
