import Rigidity.Proofs.Cluster.PlanarCoarseEnergy

/-!
# The cells of the inner square

For a triadic square `V` of scale `n` and `j < n`, the triadic squares of scale `j` meeting the
inner square `innerSquare V j` lie in it (their corners differ from that of `V` by multiples of
`3^j`); their triples lie in `V`, and every vertex lies in at most `9` of the triples. These are
the cells on which the Meyers estimate is used in the repaired Step 3 of the proof of Lemma 5.5 of
Armstrong and Dario (cells of scale `⌈n/2⌉` away from the boundary of `z + □_n`): with them, the
per-subcube bound `edgePairing_clusterExtend_sq_le_clusterForm` takes the form
`edgePairing_innerCells_sq_le`, whose remaining hypotheses are the partition scales at most `j` on
`V`, the Meyers estimate on the cells, the bound on the cell averages of the weight and the bound
on the weight.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- A triadic square of scale `j` meeting the inner square of `V` lies in it. -/
theorem TriadicCube.subset_innerSquare {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale)
    {T : TriadicCube 2} (hTs : T.scale = j) {z : Vertex 2} (hzT : z ∈ T.vertices)
    (hz : z ∈ (innerSquare V j).vertices) : T.vertices ⊆ ↑(innerSquare V j).vertices := by
  intro y hyT
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  intro i
  have hzB := (IntegerCube.mem_vertices _ z).1 hz i
  rw [cast_innerSquare_size hj] at hzB
  change V.toIntegerCube.corner i + 3 ^ j ≤ z i ∧
    z i < V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j) at hzB
  rw [cast_innerSquare_size hj]
  change V.toIntegerCube.corner i + 3 ^ j ≤ y i ∧
    y i < V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j)
  have hzT' := TriadicCube.corner_le_of_mem hzT i
  have hyT' := TriadicCube.corner_le_of_mem hyT i
  rw [hTs] at hzT' hyT'
  obtain ⟨m, hm⟩ := TriadicCube.exists_corner_sub_eq (T := T) (V := V) (by omega) i
  rw [hTs] at hm
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hj
  have hn : (3 : ℤ) ^ V.scale = 3 ^ j * (3 * 3 ^ k) := by rw [hk]; ring
  rw [hn] at hzB ⊢
  set P : ℤ := 3 ^ j with hP'
  have hPpos : 0 < P := by positivity
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have : P * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hPpos.le (by omega)
    linarith
  have hm2 : m ≤ 3 * 3 ^ k - 2 := by
    by_contra hcon
    have h3 : P * (3 * 3 ^ k - 1) ≤ P * m := mul_le_mul_of_nonneg_left (by omega) hPpos.le
    nlinarith
  have h4 : P * m ≤ P * (3 * 3 ^ k - 2) := mul_le_mul_of_nonneg_left hm2 hPpos.le
  have h5 : P * 1 ≤ P * m := mul_le_mul_of_nonneg_left hm1 hPpos.le
  constructor <;> nlinarith

/-- The cube of scale `j` of a vertex of the inner square lies in the inner square. -/
theorem cube_subset_innerSquare {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale) {x : Vertex 2}
    (hx : x ∈ (innerSquare V j).vertices) : cube j x ⊆ (innerSquare V j).vertices := by
  intro y hy
  exact TriadicCube.subset_innerSquare hj (T := ⟨j, idx j x⟩) rfl
    (mem_triadicCube_idx_iff.2 (mem_cube_self j x)) hx (mem_triadicCube_idx_iff.2 hy)

/-- The triple of the cube of scale `j` of a vertex of the inner square lies in `V`. -/
theorem enl_subset_of_mem_innerSquare {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale)
    {x : Vertex 2} (hx : x ∈ (innerSquare V j).vertices) :
    enl 1 j x ⊆ V.toIntegerCube.vertices := by
  have hsub := cube_subset_innerSquare hj hx
  have h1 := two_mul_halfSide_add_one j
  have h2 : halfSide (j + 1) = 3 * halfSide j + 1 := rfl
  have hh := halfSide_nonneg j
  intro y hy
  rw [enl, mem_box] at hy
  rw [IntegerCube.mem_vertices]
  intro i
  -- the extreme points of the cube lie in the inner square
  have hlo : (fun l => center j x l - halfSide j) ∈ (innerSquare V j).vertices :=
    hsub (by rw [cube, mem_box]; intro l; simp [abs_neg, abs_of_nonneg hh])
  have hhi : (fun l => center j x l + halfSide j) ∈ (innerSquare V j).vertices :=
    hsub (by rw [cube, mem_box]; intro l; simp [abs_of_nonneg hh])
  have hlo' := (IntegerCube.mem_vertices _ _).1 hlo i
  have hhi' := (IntegerCube.mem_vertices _ _).1 hhi i
  rw [cast_innerSquare_size hj] at hlo' hhi'
  change V.toIntegerCube.corner i + 3 ^ j ≤ center j x i - halfSide j ∧ _ at hlo'
  change _ ∧ center j x i + halfSide j <
    V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j) at hhi'
  have hs : ((V.toIntegerCube.size : ℕ) : ℤ) = 3 ^ V.scale := V.cast_toIntegerCube_size
  rw [hs]
  have hyi := abs_le.1 (hy i)
  constructor <;> omega

/-- The cells of scale `j` of the inner square of `V`, indexed by their scale and center. -/
noncomputable def innerCells (V : TriadicCube 2) (j : ℕ) : Finset (ℕ × Vertex 2) :=
  (innerSquare V j).vertices.image fun x => (j, center j x)

theorem center_mem_cube (k : ℕ) (x : Vertex 2) : center k x ∈ cube k x := by
  rw [cube, mem_box]
  intro i
  simp [halfSide_nonneg]

/-- The cells cover the inner square. -/
theorem innerCells_cover (V : TriadicCube 2) (j : ℕ) {z : Vertex 2}
    (hz : z ∈ (innerSquare V j).vertices) : ∃ c ∈ innerCells V j, z ∈ cube c.1 c.2 := by
  refine ⟨(j, center j z), Finset.mem_image_of_mem _ hz, ?_⟩
  change z ∈ cube j (center j z)
  rw [cube_eq_of_mem (center_mem_cube j z)]
  exact mem_cube_self j z

/-- The triples of the cells lie in `V`. -/
theorem innerCells_enl_subset {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale) {c : ℕ × Vertex 2}
    (hc : c ∈ innerCells V j) : enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
  change enl 1 j (center j x) ⊆ _
  rw [enl_eq_of_mem (center_mem_cube j x)]
  exact enl_subset_of_mem_innerSquare hj hx

/-- Every vertex lies in at most `9` of the triples of the cells. -/
theorem card_innerCells_filter_le (V : TriadicCube 2) (j : ℕ) (x : Vertex 2) :
    ((innerCells V j).filter fun c => x ∈ enl 1 c.1 c.2).card ≤ 9 := by
  set E : Finset (Fin 2 → ℤ) := Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ) with hE
  have hEcard : E.card = 9 := by
    rw [hE, Fintype.card_piFinset]
    simp
  have h1 := two_mul_halfSide_add_one j
  have h2 : halfSide (j + 1) = 3 * halfSide j + 1 := rfl
  have hh := halfSide_nonneg j
  have hsub : ((innerCells V j).filter fun c => x ∈ enl 1 c.1 c.2) ⊆
      E.image fun e => (j, fun i => center j x i + 3 ^ j * e i) := by
    intro c hc
    obtain ⟨hcI, hxc⟩ := Finset.mem_filter.1 hc
    obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hcI
    rw [Finset.mem_image]
    refine ⟨fun i => idx j x' i - idx j x i, ?_, ?_⟩
    · rw [hE, Fintype.mem_piFinset]
      intro i
      change x ∈ enl 1 j (center j x') at hxc
      rw [enl, mem_box] at hxc
      have hxi := hxc i
      have hxx := (mem_box.1 (show x ∈ cube j x from mem_cube_self j x)) i
      have hc1 : center j (center j x') = center j x' := by
        rw [center_eq_of_mem (center_mem_cube j x')]
      rw [hc1] at hxi
      have e1 : center j x' i = 3 ^ j * idx j x' i := rfl
      have e2 : center j x i = 3 ^ j * idx j x i := rfl
      rw [e1] at hxi
      rw [e2] at hxx
      set P : ℤ := 3 ^ j with hP
      have hPpos : 0 < P := by positivity
      have hlt : |P * (idx j x' i - idx j x i)| < 2 * P := by
        rw [mul_sub]
        rw [abs_le] at hxi hxx
        rw [abs_lt]
        constructor <;> linarith
      rw [abs_mul, abs_of_pos hPpos] at hlt
      have hlt' : |idx j x' i - idx j x i| < 2 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      rw [abs_lt] at hlt'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · ext
      · rfl
      · dsimp only
        simp only [center]
        ring
  calc ((innerCells V j).filter fun c => x ∈ enl 1 c.1 c.2).card
      ≤ (E.image fun e => (j, fun i => center j x i + 3 ^ j * e i)).card :=
        Finset.card_le_card hsub
    _ ≤ E.card := Finset.card_image_le
    _ = 9 := hEcard

/-- **The pairing of the coarsened gradient with a bounded field on a subcube, with the cells of
the inner square** (Armstrong and Dario, proof of Lemma 5.5, Steps 2 and 3, repaired, deterministic
part, in dimension two). Let `V` be a resolved triadic cube of scale `n` whose vertices have
planar partition cubes of scale at most `j < n`, `w` a function on its cluster, `g` a field with
`|g| ≤ G`, `Wt ≥ 3 planarReach` with `(avg_{□'} Wt^{3q})^{1/q} ≤ A` on the cells `□'` of scale `j`
of the inner square, `W ≥ 3 planarReach` on `𝒞(V)`, and let the Meyers estimate with exponent
`p > 1` and constant `C_M` hold on the cells. Then
`⟨∇[w]_𝒫, g⟩_V² ≤ (8 G² 9^n C² A C_M^{1/p} 9 + 64 G² 3^{n+j} C² W³) B(w, w)`. -/
theorem edgePairing_innerCells_sq_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hVr : PlanarResolved ω V) {j : ℕ} (hj : j < V.scale)
    (hres : ∀ x ∈ V.vertices, (planarPartCube ω x).scale ≤ j) (w : ClusterFun ω V)
    {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex 2 → ℝ)
    (hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z)) {W : ℝ}
    (hW : ∀ z ∈ clusterVertices ω V, 3 * planarReach ω z ≤ ENNReal.ofReal W)
    {p q CM A : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (hA : ∀ c ∈ innerCells V j, avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ q) ^ (1 / q) ≤ A)
    (hM : ∀ c ∈ innerCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ p) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ p) :
    edgePairing V.toIntegerCube.vertices g
        (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) ^ 2 ≤
      (8 * G ^ 2 * 9 ^ V.scale *
          ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
            (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 *
            (A * (CM ^ (1 / p) * ((9 : ℕ) : ℝ)))) +
        64 * G ^ 2 * 3 ^ (V.scale + j) *
          ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
            (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 * W ^ 3)) *
        clusterForm ω V w w :=
  edgePairing_clusterExtend_sq_le_clusterForm hP hVr hj hres w hg Wt hWt hW hpq hCM hA0
    (innerCells V j) (fun _ hz => innerCells_cover V j (Finset.filter_subset _ _ hz))
    (fun _ hc => innerCells_enl_subset hj hc) (fun x => card_innerCells_filter_le V j x) hA hM

end Rigidity.Proofs.Cluster
