import Rigidity.Percolation.LargePathCoalescence
import Rigidity.Percolation.OverlapPathCoalescence
import Rigidity.Percolation.Bootstrap.Relay

/-!
# Good subcubes from a crossing root and coalescence of large paths

Let the cube `z + Q_M` have a crossing root, and let all open paths of coordinate diameter at
least `D` inside it be joined inside it, where `100 (2D)^d ≤ M`. Then the cluster of the root is
a largest cluster of the cube: it crosses the cube, so it has at least `2M + 1` vertices, while
every other cluster has coordinate diameter less than `D` and so fewer than `(2D)^d` vertices.
An injective open path with at least `M / 100` steps visits more than `(2D)^d` vertices, so its
coordinate diameter is at least `D` and it is joined to the root. Hence the cube is crossing and
good in the sense of the well-connectedness input.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- The cube `z + Q_M` as an integer cube. -/
def cubeIC (z : Vertex d) (M : ℕ) : IntegerCube d := ⟨fun i => z i - M, 2 * M + 1⟩

theorem mem_cubeIC {z x : Vertex d} {M : ℕ} : x ∈ (cubeIC z M).vertices ↔ x ∈ cubeAt z M := by
  rw [IntegerCube.mem_vertices, mem_cubeAt]
  simp only [cubeIC, abs_le]
  exact forall_congr' fun i => ⟨fun h => ⟨by push_cast at h; omega, by push_cast at h; omega⟩,
    fun h => ⟨by omega, by push_cast; omega⟩⟩

theorem coe_cubeIC (z : Vertex d) (M : ℕ) :
    ((cubeIC z M).vertices : Set (Vertex d)) = cubeAt z M := by
  ext x
  exact mem_cubeIC

theorem mem_cubeIC_lowerFace {z x : Vertex d} {M : ℕ} {i : Fin d} :
    x ∈ (cubeIC z M).lowerFace i ↔ x ∈ cubeAt z M ∧ x i = z i - M := by
  rw [IntegerCube.mem_lowerFace, mem_cubeIC]
  simp [cubeIC]

theorem mem_cubeIC_upperFace {z x : Vertex d} {M : ℕ} {i : Fin d} :
    x ∈ (cubeIC z M).upperFace i ↔ x ∈ cubeAt z M ∧ x i = z i + M := by
  rw [IntegerCube.mem_upperFace, mem_cubeIC]
  simp only [cubeIC]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> push_cast at h2 ⊢ <;> omega

/-! ### Counting vertices of sets of small diameter -/

/-- A set whose vertices are within `D - 1` of a vertex in every coordinate has at most
`(2D)^d` vertices. -/
theorem ncard_le_of_close [NeZero d] {S : Set (Vertex d)} (x : Vertex d) {D : ℕ}
    (hS : ∀ y ∈ S, ∀ k, |y k - x k| < D) : S.ncard ≤ (2 * D) ^ d := by
  by_cases hD : D = 0
  · subst hD
    have : S = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      have := hS y hy 0
      push_cast at this
      linarith [abs_nonneg (y 0 - x 0)]
    simp [this]
  · have hsub : S ⊆ ↑(cubeFinset x (D - 1)) := by
      intro y hy
      rw [coe_cubeFinset]
      intro k
      have := hS y hy k
      rw [abs_lt] at this
      rw [abs_le]
      constructor <;> omega
    calc S.ncard ≤ (↑(cubeFinset x (D - 1)) : Set (Vertex d)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (2 * (D - 1) + 1) ^ d := by
          rw [Set.ncard_coe_finset]
          simp only [cubeFinset, Fintype.card_piFinset, Int.card_Icc]
          rw [Finset.prod_congr rfl (fun k _ => show (x k + ((D - 1 : ℕ) : ℤ) + 1 -
            (x k - ((D - 1 : ℕ) : ℤ))).toNat = 2 * (D - 1) + 1 by omega), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
      _ ≤ (2 * D) ^ d := Nat.pow_le_pow_left (by omega) d

/-- An injective path visiting more than `(2D)^d` vertices has coordinate diameter at least
`D`. -/
theorem pathDiameterAtLeast_of_injective [NeZero d] {n : ℕ} {γ : Fin (n + 1) → Vertex d}
    (hinj : Function.Injective γ) {D : ℕ} (hD : (2 * D) ^ d ≤ n) :
    pathDiameterAtLeast (D : ℤ) n γ := by
  by_contra h
  simp only [pathDiameterAtLeast, not_exists, not_le] at h
  have hcard := ncard_le_of_close (S := Set.range γ) (γ 0) (D := D)
    (by rintro y ⟨i, rfl⟩ k; exact h i 0 k)
  rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega

/-- Along a walk of nearest-neighbour steps every intermediate value of a coordinate is
attained. -/
theorem exists_coord_eq_of_walk {ω : Configuration d} {B : Set (Vertex d)} (k : Fin d) :
    ∀ {a b : Vertex d} (w : (openIn ω B).Walk a b) (v : ℤ), min (a k) (b k) ≤ v →
      v ≤ max (a k) (b k) → ∃ y ∈ w.support, y k = v
  | _, _, .nil, v, h1, h2 => ⟨_, List.mem_cons_self .., by simp at h1 h2; omega⟩
  | a, b, .cons (v := c) h w, v, h1, h2 => by
    by_cases hv : a k = v
    · exact ⟨a, List.mem_cons_self .., hv⟩
    · have hadj := ((openGraph_adj_iff ω a c).1 h.1).1
      have hac := abs_le.1 (abs_sub_le_one_of_nearestNeighbor_adj hadj k)
      obtain ⟨y, hy, hyv⟩ := exists_coord_eq_of_walk k w v
        (by rw [min_le_iff] at h1 ⊢; omega) (by rw [le_max_iff] at h2 ⊢; omega)
      exact ⟨y, List.mem_cons_of_mem _ hy, hyv⟩

/-- A connection inside a region as an indexed open path. -/
theorem exists_finPath_of_reachable {ω : Configuration d} {B : Set (Vertex d)} {x y : Vertex d}
    (h : (openIn ω B).Reachable x y) :
    ∃ n : ℕ, ∃ γ : Fin (n + 1) → Vertex d, γ 0 = x ∧ γ (Fin.last n) = y ∧
      ∀ i : Fin n, (openIn ω B).Adj (γ i.castSucc) (γ i.succ) := by
  obtain ⟨w⟩ := h
  refine ⟨w.length, fun j => w.getVert j.val, by simp, by simp, fun i => ?_⟩
  exact w.adj_getVert_succ i.isLt

/-- **Good subcubes.** A crossing root and the coalescence of all open paths of coordinate
diameter at least `D ≥ 1` in `z + Q_M`, with `100 (2D)^d ≤ M`, make the cube crossing and good. -/
theorem isGoodSubcube_of_root_coalesce [NeZero d] {ω : Configuration d} {z : Vertex d}
    {M D : ℕ} (hD : 1 ≤ D) (hDM : 100 * (2 * D) ^ d ≤ M) {root : Vertex d}
    (hroot : IsCrossingRoot ω ↑(cubeIC z M).vertices
      (fun i => ↑((cubeIC z M).lowerFace i)) (fun i => ↑((cubeIC z M).upperFace i)) root)
    (hcoal : LargePathsCoalesce ω ↑(cubeIC z M).vertices (pathDiameterAtLeast (D : ℤ))) :
    IsGoodSubcube ω z M ∧ IsCrossingCube ω z M := by
  classical
  rw [coe_cubeIC] at hroot hcoal
  set B := cubeAt z M with hB
  set V := {y | (openIn ω B).Reachable root y} with hV
  have hBfin : B.Finite := by
    rw [hB, ← coe_cubeIC]
    exact Finset.finite_toSet _
  have hVfin : V.Finite := hBfin.subset fun y hy => mem_of_openIn_reachable hy.symm hroot.1
  -- the crossing path
  have hroot' : IsCrossingRoot ω ↑(cubeIC z M).vertices
      (fun i => ↑((cubeIC z M).lowerFace i)) (fun i => ↑((cubeIC z M).upperFace i)) root := by
    rw [coe_cubeIC]
    exact hroot
  have hDle : 2 * D ≤ (2 * D) ^ d := Nat.le_self_pow (NeZero.ne d) _
  have h2D : 2 ≤ (2 * D) ^ d := by omega
  obtain ⟨n₀, η, hη, hrη⟩ := IntegerCube.exists_diameter_path_of_crossingRoot
    (Nat.pos_of_ne_zero (NeZero.ne d)) (cubeIC z M) (D : ℤ)
    (by simp only [cubeIC]; push_cast; omega) hroot'
  rw [coe_cubeIC] at hη hrη
  have hjoin : ∀ m (γ : Fin (m + 1) → Vertex d),
      IsSelectedOpenPath ω B (pathDiameterAtLeast (D : ℤ)) m γ → γ 0 ∈ V := by
    intro m γ hγ
    exact hrη.trans (hcoal n₀ η hη m γ hγ)
  -- every cluster not joined to the root is small
  have hsmall : ∀ x ∈ B, ¬ (openIn ω B).Reachable root x →
      ∀ y, (openIn ω B).Reachable x y → ∀ k, |y k - x k| < D := by
    intro x hx hnot y hxy k
    by_contra hk
    push Not at hk
    obtain ⟨m, γ, h0, hlast, hsteps⟩ := exists_finPath_of_reachable hxy
    have hsel : IsSelectedOpenPath ω B (pathDiameterAtLeast (D : ℤ)) m γ :=
      ⟨⟨Fin.last m, 0, k, by rw [hlast, h0]; exact hk⟩, h0 ▸ hx, hsteps⟩
    exact hnot (h0 ▸ hjoin m γ hsel)
  -- the root cluster has at least `2M + 1` vertices
  have hbig : 2 * M + 1 ≤ V.ncard := by
    have k0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    obtain ⟨⟨a, -, ha, hra⟩, ⟨b, -, hb, hrb⟩⟩ := hroot.2 k0
    have ha' := (mem_cubeIC_lowerFace.1 (Finset.mem_coe.1 ha)).2
    have hb' := (mem_cubeIC_upperFace.1 (Finset.mem_coe.1 hb)).2
    obtain ⟨w⟩ := hra.symm.trans hrb
    have himg : (↑(Finset.Icc (z k0 - M) (z k0 + M)) : Set ℤ) ⊆ (fun y => y k0) '' V := by
      intro v hv
      rw [Finset.coe_Icc, Set.mem_Icc] at hv
      obtain ⟨y, hy, hyv⟩ := exists_coord_eq_of_walk k0 w v (by rw [ha', hb']; omega)
        (by rw [ha', hb']; omega)
      exact ⟨y, hra.trans ⟨w.takeUntil y hy⟩, hyv⟩
    have hcard := Set.ncard_le_ncard himg (hVfin.image _)
    rw [Set.ncard_coe_finset, Int.card_Icc] at hcard
    have := Set.ncard_image_le (f := fun y : Vertex d => y k0) hVfin
    omega
  -- `V` is a largest cluster
  have hlargest : IsLargestClusterIn ω B V := by
    refine ⟨⟨root, hroot.1, rfl⟩, fun x hx => ?_⟩
    by_cases hrx : (openIn ω B).Reachable root x
    · have : {y | (openIn ω B).Reachable x y} = V := by
        ext y
        exact ⟨fun h => hrx.trans h, fun h => hrx.symm.trans h⟩
      rw [this]
    · have hle := ncard_le_of_close (S := {y | (openIn ω B).Reachable x y}) x
        (fun y hy => hsmall x hx hrx y hy)
      have : (2 * D) ^ d < 2 * M + 1 := by omega
      omega
  have hcross : CrossesCube z M V := by
    intro i
    obtain ⟨⟨a, -, ha, hra⟩, ⟨b, -, hb, hrb⟩⟩ := hroot.2 i
    exact ⟨⟨a, hra, (mem_cubeIC_lowerFace.1 (Finset.mem_coe.1 ha)).2⟩,
      ⟨b, hrb, (mem_cubeIC_upperFace.1 (Finset.mem_coe.1 hb)).2⟩⟩
  refine ⟨⟨V, hlargest, hcross, fun n γ hinj hsteps hn => ?_⟩, ⟨V, hlargest, hcross⟩⟩
  have hn' : (2 * D) ^ d ≤ n := by
    have : ((2 * D) ^ d : ℕ) * 100 ≤ (M : ℝ) := by exact_mod_cast (by omega : (2 * D) ^ d * 100 ≤ M)
    have : ((2 * D) ^ d : ℕ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hn1 : 0 < n := by omega
  have h0B : γ 0 ∈ B := (hsteps ⟨0, hn1⟩).2.1
  have hsel : IsSelectedOpenPath ω B (pathDiameterAtLeast (D : ℤ)) n γ :=
    ⟨pathDiameterAtLeast_of_injective hinj hn', h0B, hsteps⟩
  exact ⟨root, SimpleGraph.Reachable.refl _, (hjoin n γ hsel).symm⟩

end Rigidity.Percolation
