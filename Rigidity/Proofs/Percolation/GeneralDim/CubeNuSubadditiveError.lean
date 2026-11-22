import Rigidity.Proofs.Percolation.GeneralDim.CubeSubadditive
import Rigidity.Proofs.Percolation.GeneralDim.CubeBoundaryErrorBound

/-!
# The error in the subadditivity of `ν` on triadic cubes of `ℤ^d`

A vertex `x` is *exceptional at scale `n`* when its subcube `V(x)` of scale `n` is not resolved,
or the region `□.parent ∪ (x + Q_{s-1})` of the local path from `x` to the anchor of its partition
cube `□` (side `s`) leaves `V(x)`. On the partition event, at a vertex `x` of `C_*(U)` which is not
exceptional, every open edge `{x, y}` of `C_*(U)` lies in the cluster of `V(x)`: the local path
from `x` to the anchor stays in `V(x)`, and the anchor lies in `C_*(V(x))`. So the flux error in
the subadditivity of `ν` is carried by the open edges at exceptional vertices, and by the
Cauchy–Schwarz inequality, the energy bound `B(v, v) ≤ 2 |U| ν(U, p) ≤ (3^d/2) |U| |p|₁²` and
Young's inequality,

`|U| ν(U, p) ≤ ∑_{x ∈ U} ν(V(x), p) + (3^d/4) |p|₁² (s G + |U| / s)`

for every `s > 0`, where `G` is the number of exceptional vertices of `C_*(U)` (Armstrong and
Dario, proof of Lemma 4.8, (4.33): the set of exceptional vertices plays the role of the set of
vertices near the boundaries of the subcubes in their proof).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- A vertex is exceptional at scale `n` when its subcube of scale `n` is unresolved or the
region of its local path to the anchor of its partition cube leaves this subcube. -/
def IsSubcubeExceptional (ω : Configuration d) (n : ℕ) (x : Vertex d) : Prop :=
  ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
    (partitionCube ω x).parent.vertices ∪ cubeAt x (3 ^ (partitionCube ω x).scale - 1) ⊆
      (triadicCubeAt n x).vertices)

/-- **Open edges at non-exceptional vertices lie in the cluster of the subcube.** -/
theorem isResolvedSubcubePair_of_not_isSubcubeExceptional (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) {x y : Vertex d}
    (hx : x ∈ crossingClusterVertices ω U) (hxy : (openGraph ω).Adj x y)
    (hne : ¬ IsSubcubeExceptional ω n x) : IsResolvedSubcubePair ω n x y := by
  unfold IsSubcubeExceptional at hne
  rw [not_not] at hne
  obtain ⟨hV, hreg⟩ := hne
  set V := triadicCubeAt n x
  have hxC := mem_crossingClusterVertices.1 hx
  have hxU := U.crossingCluster_subset ω hxC
  have hxV : x ∈ V.vertices := mem_triadicCubeAt n x
  have hscale : (partitionCube ω x).scale ≤ U.scale :=
    (hV x hxV).trans (by rw [scale_triadicCubeAt]; exact hn)
  have hpath := reachable_partitionAnchor_of_mem_crossingCluster hd hP hxU hscale hxC
  have hpathV : (openIn ω V.vertices).Reachable x (partitionAnchor ω x) :=
    reachable_openIn_mono (fun z hz => hreg hz.2) hpath
  have hanchor : partitionAnchor ω x ∈ V.crossingCluster ω :=
    crossingCluster_partitionCube_subset hd hP hxV (hV x hxV)
      (partitionAnchor_mem_crossingCluster hP x)
  obtain ⟨r, hr, hra⟩ := hanchor
  have hxVC : x ∈ V.crossingCluster ω := ⟨r, hr, hra.trans hpathV.symm⟩
  have hyV : y ∈ V.vertices := by
    refine hreg (Or.inr fun i => ?_)
    have h1 := abs_sub_le_one_of_adj_lattice (openGraph_le ω hxy) i
    have h3 := three_le_scale_partitionCube hP x
    have h27 : (27 : ℕ) ≤ 3 ^ (partitionCube ω x).scale :=
      (Nat.pow_le_pow_right (by norm_num) h3).trans' (by norm_num)
    have hcast : ((3 ^ (partitionCube ω x).scale - 1 : ℕ) : ℤ) ≥ 1 := by
      have : 1 ≤ 3 ^ (partitionCube ω x).scale - 1 := by omega
      exact_mod_cast this
    rw [abs_sub_comm] at h1
    exact h1.trans hcast
  exact ⟨hV, mem_crossingClusterVertices.2 hxVC,
    mem_crossingClusterVertices.2 (mem_crossingCluster_of_adj hxVC hyV hxy)⟩

/-- The number of exceptional vertices of the cluster of `U` at scale `n`. -/
noncomputable def subcubeExceptionalCount (ω : Configuration d) (U : TriadicCube d) (n : ℕ) : ℝ :=
  (((crossingClusterVertices ω U).filter (IsSubcubeExceptional ω n)).card : ℝ)

/-- **The flux error is carried by the exceptional vertices.** -/
theorem flux_error_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d} {n : ℕ}
    (hn : n ≤ U.scale) (p : Fin d → ℝ) (v : CubeFun ω U) {s : ℝ} (hs : 0 < s)
    (hB : 2 * cubeForm ω U v v ≤ 3 ^ d * U.latticeVolume * (∑ i, |p i|) ^ 2) :
    (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω U, ∑ y ∈ crossingClusterVertices ω U,
        (if IsResolvedSubcubePair ω n x y then 0 else cubeFluxTerm ω U p v x y) ≤
      3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
        (s * subcubeExceptionalCount ω U n + U.latticeVolume / s) := by
  set C := crossingClusterVertices ω U
  set f := cubeExtend ω U v
  set P := ∑ i, |p i| with hPdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set X := ∑ x ∈ C, ∑ y ∈ C,
    (if IsSubcubeExceptional ω n x ∧ (openGraph ω).Adj x y then |f x - f y| else 0) with hX
  -- each exceptional term is at most `P |f x - f y|`
  have hterm : ∀ x ∈ C, ∀ y ∈ C, (if IsResolvedSubcubePair ω n x y then 0
      else cubeFluxTerm ω U p v x y) ≤ P * (if IsSubcubeExceptional ω n x ∧ (openGraph ω).Adj x y then
        |f x - f y| else 0) := by
    intro x hx y _
    by_cases hpair : IsResolvedSubcubePair ω n x y
    · rw [if_pos hpair]
      exact mul_nonneg hP0 (by split_ifs <;> positivity)
    · rw [if_neg hpair]
      simp only [cubeFluxTerm]
      by_cases hxy : (openGraph ω).Adj x y
      · have hEx : IsSubcubeExceptional ω n x := by
          by_contra hne
          exact hpair (isResolvedSubcubePair_of_not_isSubcubeExceptional hd hP hn hx hxy hne)
        rw [if_pos hxy, if_pos ⟨hEx, hxy⟩]
        have ha := abs_sum_mul_sub_le_of_adj (p := p) hxy
        calc (∑ i, p i * ((y i : ℝ) - x i)) * (f y - f x)
            ≤ |(∑ i, p i * ((y i : ℝ) - x i)) * (f y - f x)| := le_abs_self _
          _ = |∑ i, p i * ((y i : ℝ) - x i)| * |f x - f y| := by rw [abs_mul, abs_sub_comm (f y)]
          _ ≤ P * |f x - f y| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      · rw [if_neg hxy, if_neg (fun h => hxy h.2), mul_zero]
  have hsum : ∑ x ∈ C, ∑ y ∈ C, (if IsResolvedSubcubePair ω n x y then 0
      else cubeFluxTerm ω U p v x y) ≤ P * X := by
    rw [hX, Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y hy => hterm x hx y hy
  -- Cauchy–Schwarz
  set a : Vertex d × Vertex d → ℝ := fun e =>
    if IsSubcubeExceptional ω n e.1 ∧ (openGraph ω).Adj e.1 e.2 then 1 else 0
  set b : Vertex d × Vertex d → ℝ := fun e =>
    if (openGraph ω).Adj e.1 e.2 then |f e.1 - f e.2| else 0
  have hXab : X = ∑ e ∈ C ×ˢ C, a e * b e := by
    rw [hX, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases h : IsSubcubeExceptional ω n x ∧ (openGraph ω).Adj x y
    · rw [if_pos h]
      simp only [a, b, if_pos h, if_pos h.2, one_mul]
    · rw [if_neg h]
      simp only [a, b, if_neg h, zero_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (C ×ˢ C) a b
  have hb2 : ∑ e ∈ C ×ˢ C, b e ^ 2 = 2 * cubeForm ω U v v := by
    rw [cubeForm_self_eq_sum, Finset.sum_product]
    rw [show (2 : ℝ) * ((1 / 2) * ∑ x ∈ C, ∑ y ∈ C, (if (openGraph ω).Adj x y then
        (f x - f y) * (f x - f y) else 0)) = ∑ x ∈ C, ∑ y ∈ C, (if (openGraph ω).Adj x y then
        (f x - f y) * (f x - f y) else 0) by ring]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [b]
    split_ifs
    · rw [sq_abs, sq]
    · simp
  have ha2 : ∑ e ∈ C ×ˢ C, a e ^ 2 ≤ 3 ^ d * subcubeExceptionalCount ω U n := by
    rw [Finset.sum_product]
    have hrow : ∀ x ∈ C, ∑ y ∈ C, a (x, y) ^ 2 ≤
        if IsSubcubeExceptional ω n x then (3 : ℝ) ^ d else 0 := by
      intro x _
      by_cases hEx : IsSubcubeExceptional ω n x
      · rw [if_pos hEx]
        have hcard := card_filter_openGraph_adj_le (ω := ω) C x
        have hcard' : ((C.filter fun y => (openGraph ω).Adj x y).card : ℝ) ≤ 3 ^ d := by
          exact_mod_cast hcard
        calc ∑ y ∈ C, a (x, y) ^ 2 = ((C.filter fun y => (openGraph ω).Adj x y).card : ℝ) := by
              rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
              refine Finset.sum_congr rfl fun y _ => ?_
              simp only [a, hEx, true_and]
              split_ifs <;> simp
          _ ≤ 3 ^ d := hcard'
      · rw [if_neg hEx]
        refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_)
        simp only [a, hEx, false_and, if_false]
        norm_num
    calc ∑ x ∈ C, ∑ y ∈ C, a (x, y) ^ 2 ≤
          ∑ x ∈ C, (if IsSubcubeExceptional ω n x then (3 : ℝ) ^ d else 0) :=
          Finset.sum_le_sum hrow
      _ = 3 ^ d * subcubeExceptionalCount ω U n := by
          rw [subcubeExceptionalCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
            Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> simp
  have hG0 : 0 ≤ subcubeExceptionalCount ω U n := Nat.cast_nonneg _
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
    split_ifs <;> positivity
  have hsq : X ^ 2 ≤ (3 ^ d * subcubeExceptionalCount ω U n) * (2 * cubeForm ω U v v) := by
    rw [hXab]
    calc (∑ e ∈ C ×ˢ C, a e * b e) ^ 2
        ≤ (∑ e ∈ C ×ˢ C, a e ^ 2) * ∑ e ∈ C ×ˢ C, b e ^ 2 := hcs
      _ ≤ (3 ^ d * subcubeExceptionalCount ω U n) * (2 * cubeForm ω U v v) := by
          rw [hb2]
          exact mul_le_mul_of_nonneg_right ha2
            (mul_nonneg (by norm_num) (cubeForm_self_nonneg v))
  have hvol := U.latticeVolume_pos
  by_cases hp : P = 0
  · have : P * X = 0 := by rw [hp, zero_mul]
    rw [hp]
    have h1 := hsum
    rw [this] at h1
    nlinarith [hG0, hvol, hs]
  · have hPpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hp)
    have hτ : 0 < 1 / (s * P) := by positivity
    have hY := le_half_div_add_mul_of_sq_le hX0 (by positivity)
      (mul_nonneg (by norm_num) (cubeForm_self_nonneg v)) hτ hsq
    have hY' : X ≤ (3 ^ d * subcubeExceptionalCount ω U n * (s * P) +
        3 ^ d * U.latticeVolume * P ^ 2 / (s * P)) / 2 := by
      refine hY.trans ?_
      rw [div_div_eq_mul_div, div_one]
      gcongr
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hB (by positivity)
    have hfinal : (1 / 2 : ℝ) * (P * X) ≤ 3 ^ d / 4 * P ^ 2 *
        (s * subcubeExceptionalCount ω U n + U.latticeVolume / s) := by
      have e : 3 ^ d * U.latticeVolume * P ^ 2 / (s * P) = 3 ^ d * U.latticeVolume * P / s := by
        field_simp
      rw [e] at hY'
      have h2 : (1 / 2 : ℝ) * (P * X) ≤ (1 / 2) * (P * ((3 ^ d * subcubeExceptionalCount ω U n *
          (s * P) + 3 ^ d * U.latticeVolume * P / s) / 2)) := by gcongr
      refine h2.trans (le_of_eq ?_)
      field_simp
      ring
    linarith

/-- **Subadditivity of `ν` with the exceptional vertices** (Armstrong and Dario, proof of
Lemma 4.8, (4.33)). On the partition event, for every `s > 0`,
`|U| ν(U, p) ≤ ∑_{x ∈ U} ν(V(x), p) + (3^d/4) |p|₁² (s G + |U| / s)`, where `G` is the number of
exceptional vertices of `C_*(U)` at scale `n`. -/
theorem cubeNu_mul_latticeVolume_le_sum_add (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) (p : Fin d → ℝ) {s : ℝ} (hs : 0 < s) :
    cubeNu ω U p * U.latticeVolume ≤
      ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p +
        3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
          (s * subcubeExceptionalCount ω U n + U.latticeVolume / s) := by
  obtain ⟨v, hv, hvar, hle⟩ := cubeNu_le_sum_subcubes hd hP hn p
  have hdrop : ∑ x ∈ U.toIntegerCube.vertices,
      (if PartitionResolved ω (triadicCubeAt n x) then cubeNu ω (triadicCubeAt n x) p else 0) ≤
      ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p :=
    Finset.sum_le_sum fun x _ => by
      split_ifs
      · exact le_rfl
      · exact cubeNu_nonneg p
  have hB : 2 * cubeForm ω U v v ≤ 3 ^ d * U.latticeVolume * (∑ i, |p i|) ^ 2 := by
    have h1 := cubeForm_le_of_cubeNu_variation p hv hvar
    have h2 := cubeNu_le (ω := ω) (U := U) p
    have hvol := U.latticeVolume_pos
    nlinarith
  have herr := flux_error_le hd hP hn p v hs hB
  linarith

end Rigidity.Percolation
