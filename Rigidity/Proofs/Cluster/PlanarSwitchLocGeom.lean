import Rigidity.Proofs.Cluster.PlanarSwitchLocCore

/-!
# Counting for the comparison of display (5.31)

On a resolved triadic cube `U` whose partition cubes have scale at most `k`, a vertex lies in the
coarsening windows of at most `2 (10 · 3^k + 3)²` lattice edges of `U`
(`coarseWeight_le_of_scale_le`), and every window has at most `2 · 81 · 9^k` vertices
(`card_coarseEdgeWindow_le_of_scale_le`): the windows lie in the squares of side `9s` around the
partition cubes of the endpoints.

The interior square `interiorCube V r` of a triadic cube `V` consists of its vertices at distance
more than `r` from the complement; `V` minus its interior square has at most `4 r 3ⁿ` vertices.
A field bounded by `H` has squared edge norm at most `2 |U| H²`, and the part of it on the lattice
edges of `U` not inside a set `D` has squared edge norm at most `4 |U \ D| H²`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- A point of the square of side `9s` around a triadic cube is within `5s` of each vertex of the
cube. -/
theorem abs_sub_le_of_mem_ninefold {Q : TriadicCube 2} {x a : Vertex 2} (hx : x ∈ Q.vertices)
    (ha : a ∈ (↑Q.ninefold.vertices : Set (Vertex 2))) (i : Fin 2) :
    |a i - x i| ≤ 5 * 3 ^ Q.scale := by
  rw [TriadicCube.mem_ninefold] at ha
  have h1 := ha i
  have h2 := Q.abs_sub_center_le hx i
  have h4 := Q.two_mul_ninefoldRadius
  have h5 := abs_sub_le (a i) (Q.center i) (x i)
  rw [abs_sub_comm (Q.center i) (x i)] at h5
  linarith

/-- The square of side `2R + 1` centred at a vertex. -/
def boxAround (a : Vertex 2) (R : ℕ) : IntegerCube 2 := ⟨fun i => a i - R, 2 * R + 1⟩

theorem mem_boxAround {a x : Vertex 2} {R : ℕ} :
    x ∈ (boxAround a R).vertices ↔ ∀ i, |x i - a i| ≤ R := by
  rw [IntegerCube.mem_vertices]
  refine forall_congr' fun i => ?_
  simp only [boxAround, abs_le]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **The number of windows containing a vertex.** -/
theorem coarseWeight_le_of_scale_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {k : ℕ} (hk : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ k)
    (a : Vertex 2) : coarseWeight ω U a ≤ 2 * (10 * 3 ^ k + 3) ^ 2 := by
  set R : ℕ := 5 * 3 ^ k + 1 with hR
  have hsub : (latticeEdgesIn U).filter
      (fun k' => a ∈ coarseEdgeWindow ω U k'.1 (k'.1 + unitVertex k'.2)) ⊆
      (boxAround a R).vertices ×ˢ (Finset.univ : Finset (Fin 2)) := by
    intro k' hk'
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk'
    obtain ⟨hk1a, hk1b⟩ := Finset.mem_filter.1 hk1
    have hx : k'.1 ∈ U.vertices :=
      (U.mem_toIntegerCube_vertices _).1 (Finset.mem_product.1 hk1a).1
    have hy : k'.1 + unitVertex k'.2 ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hk1b
    refine Finset.mem_product.2 ⟨mem_boxAround.2 fun i => ?_, Finset.mem_univ _⟩
    have h3 : (3 : ℤ) ^ (planarPartCube ω k'.1).scale ≤ 3 ^ k :=
      pow_le_pow_right₀ (by norm_num) (hk _ hx)
    have h3' : (3 : ℤ) ^ (planarPartCube ω (k'.1 + unitVertex k'.2)).scale ≤ 3 ^ k :=
      pow_le_pow_right₀ (by norm_num) (hk _ hy)
    have hu : |(k'.1 + unitVertex k'.2) i - k'.1 i| ≤ 1 := by
      rw [abs_sub_comm]
      exact abs_sub_unitVertex_le k'.1 k'.2 i
    have hRc : ((R : ℕ) : ℤ) = 5 * 3 ^ k + 1 := by rw [hR]; push_cast; ring
    rw [abs_sub_comm, hRc]
    rcases mem_ninefold_of_mem_coarseEdgeWindow hP hU hx hy (abs_sub_unitVertex_le k'.1 k'.2)
      hk2 with h | h
    · have := abs_sub_le_of_mem_ninefold (planarPartCube_spec hP k'.1).1 h i
      linarith
    · have := abs_sub_le_of_mem_ninefold (planarPartCube_spec hP _).1 h i
      have h6 := abs_sub_le (a i) ((k'.1 + unitVertex k'.2) i) (k'.1 i)
      linarith
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, IntegerCube.card_vertices, Finset.card_univ, Fintype.card_fin] at hcard
  unfold coarseWeight
  rw [Finset.sum_boole]
  have hc : (((boxAround a R).size ^ 2 * 2 : ℕ) : ℝ) = 2 * (10 * 3 ^ k + 3) ^ 2 := by
    simp only [boxAround, hR]
    push_cast
    ring
  rw [← hc]
  exact_mod_cast hcard

/-- **The size of the windows.** -/
theorem card_coarseEdgeWindow_le_of_scale_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {k : ℕ} (hk : ∀ x ∈ U.vertices, (planarPartCube ω x).scale ≤ k)
    {x y : Vertex 2} (hx : x ∈ U.vertices) (hy : y ∈ U.vertices) (hnear : ∀ i, |x i - y i| ≤ 1) :
    ((coarseEdgeWindow ω U x y).card : ℝ) ≤ 2 * 81 * 9 ^ k := by
  have hsub : coarseEdgeWindow ω U x y ⊆
      (planarPartCube ω x).ninefold.vertices ∪ (planarPartCube ω y).ninefold.vertices := by
    intro a ha
    rcases mem_ninefold_of_mem_coarseEdgeWindow hP hU hx hy hnear ha with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [IntegerCube.card_vertices, IntegerCube.card_vertices] at hcard
  have hQ : ∀ Q : TriadicCube 2, Q.scale ≤ k → ((Q.ninefold.size ^ 2 : ℕ) : ℝ) ≤ 81 * 9 ^ k := by
    intro Q hQ
    have : Q.ninefold.size = 9 * 3 ^ Q.scale := rfl
    rw [this]
    push_cast
    have h9 : (9 : ℝ) ^ Q.scale ≤ 9 ^ k := pow_le_pow_right₀ (by norm_num) hQ
    have e : ((9 : ℝ) * 3 ^ Q.scale) ^ 2 = 81 * 9 ^ Q.scale := by
      rw [mul_pow, ← pow_mul, mul_comm Q.scale 2, pow_mul]
      norm_num
    rw [e]
    linarith
  have h1 := hQ _ (hk x hx)
  have h2 := hQ _ (hk y hy)
  have hc : ((coarseEdgeWindow ω U x y).card : ℝ) ≤
      (((planarPartCube ω x).ninefold.size ^ 2 : ℕ) : ℝ) +
        (((planarPartCube ω y).ninefold.size ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- The interior square of a triadic cube: its vertices at distance more than `r` from the
complement. -/
def interiorCube (V : TriadicCube 2) (r : ℕ) : IntegerCube 2 :=
  ⟨fun i => V.toIntegerCube.corner i + r, 3 ^ V.scale - 2 * r⟩

theorem mem_toIntegerCube_vertices_of_near_interiorCube {V : TriadicCube 2} {r : ℕ}
    (h2r : 2 * r ≤ 3 ^ V.scale) {x y : Vertex 2} (hx : x ∈ (interiorCube V r).vertices)
    (hy : ∀ i, |y i - x i| ≤ r) : y ∈ V.toIntegerCube.vertices := by
  rw [IntegerCube.mem_vertices] at hx ⊢
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have h3 := abs_le.1 (hy i)
  have hsz : ((3 ^ V.scale - 2 * r : ℕ) : ℤ) = 3 ^ V.scale - 2 * r := by
    push_cast [Nat.cast_sub h2r]
    ring
  simp only [interiorCube] at h1 h2
  rw [hsz] at h2
  have hsz' : ((V.toIntegerCube.size : ℕ) : ℤ) = 3 ^ V.scale := by
    change (((3 ^ V.scale : ℕ)) : ℤ) = _
    push_cast
    ring
  rw [hsz']
  constructor <;> linarith [h3.1, h3.2]

theorem interiorCube_subset {V : TriadicCube 2} {r : ℕ} (h2r : 2 * r ≤ 3 ^ V.scale) :
    (interiorCube V r).vertices ⊆ V.toIntegerCube.vertices := fun x hx =>
  mem_toIntegerCube_vertices_of_near_interiorCube h2r hx fun i => by simp

/-- **The boundary layer is small.** -/
theorem card_sdiff_interiorCube_le {V : TriadicCube 2} {r : ℕ} (h2r : 2 * r ≤ 3 ^ V.scale) :
    ((V.toIntegerCube.vertices \ (interiorCube V r).vertices).card : ℝ) ≤
      4 * r * 3 ^ V.scale := by
  rw [Finset.card_sdiff_of_subset (interiorCube_subset h2r), IntegerCube.card_vertices,
    IntegerCube.card_vertices]
  have hle : (3 ^ V.scale - 2 * r) ^ 2 ≤ V.toIntegerCube.size ^ 2 := by
    change (3 ^ V.scale - 2 * r) ^ 2 ≤ (3 ^ V.scale) ^ 2
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  have hsize : (interiorCube V r).size = 3 ^ V.scale - 2 * r := rfl
  rw [hsize, Nat.cast_sub hle]
  have hs : V.toIntegerCube.size = 3 ^ V.scale := rfl
  rw [hs]
  push_cast [Nat.cast_sub h2r]
  nlinarith [sq_nonneg ((r : ℝ))]

/-- A bounded field has squared edge norm at most `2 |U| H²`. -/
theorem edgeNormSq_le {U : TriadicCube 2} {h : Vertex 2 → Fin 2 → ℝ} {H : ℝ}
    (hh : ∀ x i, |h x i| ≤ H) : edgeNormSq U h ≤ 2 * U.volume * H ^ 2 := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hh 0 0)
  calc edgeNormSq U h ≤ ∑ _k ∈ latticeEdgesIn U, H ^ 2 :=
        Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hh _ _) 2
    _ = ((latticeEdgesIn U).card : ℝ) * H ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * U.volume * H ^ 2 :=
        mul_le_mul_of_nonneg_right (card_latticeEdgesIn_le U) (sq_nonneg _)

theorem edgeNormSq_restrictField_le (U : TriadicCube 2) (D : Finset (Vertex 2))
    (h : Vertex 2 → Fin 2 → ℝ) : edgeNormSq U (restrictField D h) ≤ edgeNormSq U h :=
  Finset.sum_le_sum fun k _ => by
    simp only [restrictField]
    split_ifs
    · exact le_rfl
    · rw [sq, zero_mul]
      exact sq_nonneg _

/-- **The part of a field off the edges inside `D`.** -/
theorem edgeNormSq_sub_restrictField_le (U : TriadicCube 2) (D : Finset (Vertex 2))
    {h : Vertex 2 → Fin 2 → ℝ} {H : ℝ} (hh : ∀ x i, |h x i| ≤ H) :
    edgeNormSq U (h - restrictField D h) ≤
      4 * ((U.toIntegerCube.vertices \ D).card : ℝ) * H ^ 2 := by
  set S := U.toIntegerCube.vertices \ D with hS
  set A := (latticeEdgesIn U).filter (fun k => k.1 ∉ D) with hA
  set B := (latticeEdgesIn U).filter (fun k => k.1 + unitVertex k.2 ∉ D) with hB
  have hpt : ∀ k ∈ latticeEdgesIn U, (h - restrictField D h) k.1 k.2 ^ 2 ≤
      H ^ 2 * ((if k.1 ∉ D then 1 else 0) + (if k.1 + unitVertex k.2 ∉ D then 1 else 0)) := by
    intro k _
    have hk2 : h k.1 k.2 ^ 2 ≤ H ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hh _ _) 2
    simp only [Pi.sub_apply, restrictField]
    by_cases h1 : k.1 ∈ D <;> by_cases h2 : k.1 + unitVertex k.2 ∈ D <;>
      simp [h1, h2] <;> nlinarith [sq_nonneg H]
  have hAc : A.card ≤ S.card * 2 := by
    calc A.card ≤ (S ×ˢ (Finset.univ : Finset (Fin 2))).card := by
          refine Finset.card_le_card fun k hk => ?_
          obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
          obtain ⟨hk1a, _⟩ := Finset.mem_filter.1 hk1
          exact Finset.mem_product.2 ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_product.1 hk1a).1, hk2⟩,
            Finset.mem_univ _⟩
      _ = S.card * 2 := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hBc : B.card ≤ S.card * 2 := by
    calc B.card ≤ (S ×ˢ (Finset.univ : Finset (Fin 2))).card := by
          refine Finset.card_le_card_of_injOn (fun k => (k.1 + unitVertex k.2, k.2)) ?_ ?_
          · intro k hk
            obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
            obtain ⟨_, hk1b⟩ := Finset.mem_filter.1 hk1
            exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_sdiff.2 ⟨hk1b, hk2⟩,
              Finset.mem_univ _⟩)
          · intro k _ k' _ hkk
            simp only [Prod.mk.injEq] at hkk
            obtain ⟨h1, h2⟩ := hkk
            rw [h2] at h1
            exact Prod.ext (add_right_cancel h1) h2
      _ = S.card * 2 := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  calc edgeNormSq U (h - restrictField D h)
      ≤ ∑ k ∈ latticeEdgesIn U, H ^ 2 *
          ((if k.1 ∉ D then 1 else 0) + (if k.1 + unitVertex k.2 ∉ D then 1 else 0)) :=
        Finset.sum_le_sum hpt
    _ = H ^ 2 * ((A.card : ℝ) + B.card) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
    _ ≤ H ^ 2 * ((S.card * 2 : ℕ) + (S.card * 2 : ℕ)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (sq_nonneg _) <;> exact_mod_cast ‹_›
    _ = 4 * (S.card : ℝ) * H ^ 2 := by push_cast; ring

end Rigidity.Proofs.Cluster
