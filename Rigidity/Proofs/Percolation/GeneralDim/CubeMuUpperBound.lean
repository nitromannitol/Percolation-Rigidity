import Rigidity.Proofs.Percolation.GeneralDim.CubeVariations
import Rigidity.Proofs.Percolation.GeneralDim.CubeStokes

/-!
# Upper bound for `-μ` on triadic cubes of `ℤ^d`

The coarse pairing `ℓ_q w` is at most `|q|₁ √(2d) ∑_{x ∈ U} |∇[w]_𝒫|(x)`. By Lemma 3.3 of Armstrong
and Dario with `s = 1` (`partition_sum_gradNormIn_coarseAnchor_rpow_le`) and the Cauchy–Schwarz
inequality,

`∑_{x ∈ U} |∇[w]_𝒫|(x) ≤ C₃ ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{d-1} |∇w 1_{a≠0}|(z)
  ≤ C₃ (∑_{z ∈ C_*(U)} size(□_𝒫(z))^{2d-2})^{1/2} B(w, w)^{1/2}`,

and Young's inequality gives, on the partition event and for a resolved cube,

`-μ(U, q) ≤ d C₃² |q|₁² |U|⁻¹ ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{2d-2}`

(Armstrong and Dario, Lemma 4.4, (4.12), with the average over the cluster `C_*(U) ⊆ U`). By the
first variation, the energy of the minimizer is `-2 |U| μ(U, q)`, which gives (4.20).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The constant of Lemma 3.3 of Armstrong and Dario for the partition into good cubes, with
`s = 1`. -/
noncomputable def coarseGradConstant (d : ℕ) : ℝ :=
  2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) * (2 * √(d : ℝ))

theorem coarseGradConstant_nonneg (d : ℕ) : 0 ≤ coarseGradConstant d := by
  unfold coarseGradConstant
  positivity

/-- The increments of a function along the lattice edges `{x, x + e_i}` inside a set are bounded by
the magnitude of its lattice gradient at `x`. -/
theorem sum_ite_abs_add_unit_sub_le (S : Finset (Vertex d)) (f : Vertex d → ℝ) (x : Vertex d) :
    ∑ i : Fin d, (if x + LatticeProb.unit i ∈ S then |f (x + LatticeProb.unit i) - f x| else 0) ≤
      √(2 * (d : ℝ)) * gradNormIn (nearestNeighborGraph d) S f x := by
  obtain ⟨g, hg⟩ : ∃ g : Vertex d → ℝ,
      g = fun y => if (nearestNeighborGraph d).Adj x y then (f x - f y) ^ 2 else 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin d → ℝ, b = fun i =>
      if x + LatticeProb.unit i ∈ S then |f (x + LatticeProb.unit i) - f x| else 0 := ⟨_, rfl⟩
  have hg0 : ∀ y, 0 ≤ g y := fun y => by simp only [hg]; split_ifs <;> positivity
  have hinj : ∀ i ∈ Finset.univ.filter (fun i : Fin d => x + LatticeProb.unit i ∈ S),
      ∀ j ∈ Finset.univ.filter (fun i : Fin d => x + LatticeProb.unit i ∈ S),
      x + LatticeProb.unit i = x + LatticeProb.unit j → i = j := by
    intro i _ j _ hij
    by_contra hne
    have h := congrFun hij i
    simp only [Pi.add_apply, unit_apply_self, unit_apply_ne hne] at h
    omega
  have hb2 : ∑ i, b i ^ 2 ≤ ∑ y ∈ S, g y := by
    have e1 : ∑ i, b i ^ 2 = ∑ i ∈ Finset.univ.filter (fun i : Fin d =>
        x + LatticeProb.unit i ∈ S), g (x + LatticeProb.unit i) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hb, hg]
      split_ifs with h1 h2
      · rw [sq_abs]
        ring
      · exact absurd ⟨i, Or.inl rfl⟩ h2
      · simp
    rw [e1, ← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => hg0 y
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    exact (Finset.mem_filter.1 hi).2
  have hgrad : ∑ y ∈ S, g y = 2 * gradNormIn (nearestNeighborGraph d) S f x ^ 2 := by
    rw [gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => by
      split_ifs <;> positivity))]
    simp only [hg]
    ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := b)
  rw [Finset.card_univ, Fintype.card_fin] at hcs
  have hb0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => by
    simp only [hb]; split_ifs <;> positivity
  have hrhs : 0 ≤ √(2 * (d : ℝ)) * gradNormIn (nearestNeighborGraph d) S f x :=
    mul_nonneg (Real.sqrt_nonneg _) (gradNormIn_nonneg _ _ _ _)
  have hbsum : ∑ i : Fin d, (if x + LatticeProb.unit i ∈ S then
      |f (x + LatticeProb.unit i) - f x| else 0) = ∑ i, b i := by
    rw [hb]
  rw [hbsum]
  refine (pow_le_pow_iff_left₀ hb0 hrhs two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc (∑ i, b i) ^ 2 ≤ (d : ℝ) * ∑ i, b i ^ 2 := hcs
    _ ≤ (d : ℝ) * (2 * gradNormIn (nearestNeighborGraph d) S f x ^ 2) := by
        rw [← hgrad]
        exact mul_le_mul_of_nonneg_left hb2 (Nat.cast_nonneg d)
    _ = 2 * d * gradNormIn (nearestNeighborGraph d) S f x ^ 2 := by ring

/-- **The coarse pairing is controlled by the coarsened gradient.** -/
theorem abs_cubeCoarsePairing_le_sum_gradNormIn {U : TriadicCube d} (q : Fin d → ℝ)
    (w : CubeFun ω U) :
    |cubeCoarsePairing ω U q w| ≤ (∑ i, |q i|) * √(2 * (d : ℝ)) *
      ∑ x ∈ U.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices (cubeCoarsen ω U w) x := by
  rw [cubeCoarsePairing_apply, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hq : ∀ i, |q i| ≤ ∑ j, |q j| := fun i =>
    Finset.single_le_sum (f := fun j => |q j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  calc ∑ i, |if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then
          q i * (cubeExtend ω U w (partitionAnchor ω (x + LatticeProb.unit i)) -
            cubeExtend ω U w (partitionAnchor ω x)) else 0|
      ≤ ∑ i, (∑ j, |q j|) * (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then
          |cubeCoarsen ω U w (x + LatticeProb.unit i) - cubeCoarsen ω U w x| else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hq i) (abs_nonneg _)
        · simp
    _ = (∑ j, |q j|) * ∑ i, (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then
          |cubeCoarsen ω U w (x + LatticeProb.unit i) - cubeCoarsen ω U w x| else 0) := by
        rw [Finset.mul_sum]
    _ ≤ (∑ j, |q j|) * (√(2 * (d : ℝ)) * gradNormIn (nearestNeighborGraph d)
          U.toIntegerCube.vertices (cubeCoarsen ω U w) x) :=
        mul_le_mul_of_nonneg_left (sum_ite_abs_add_unit_sub_le _ _ x)
          (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ = _ := by ring

/-- The energy as the sum of the squared magnitudes of the open gradient on the cluster. -/
theorem sum_gradNormIn_sq_eq_cubeForm {U : TriadicCube d} (w : CubeFun ω U) :
    ∑ z ∈ crossingClusterVertices ω U,
        gradNormIn (openGraph ω) (crossingClusterVertices ω U) (cubeExtend ω U w) z ^ 2 =
      cubeForm ω U w w := by
  rw [cubeForm_self_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => by
    split_ifs <;> positivity))]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- **Coarse pairing and energy** (Armstrong and Dario, proof of Lemma 4.4, (4.14)): on the
partition event and for a resolved cube,
`ℓ_q(w)² ≤ 2d C₃² |q|₁² (∑_{z ∈ C_*(U)} size(□_𝒫(z))^{2d-2}) B(w, w)`. -/
theorem sq_cubeCoarsePairing_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) (w : CubeFun ω U) :
    cubeCoarsePairing ω U q w ^ 2 ≤
      2 * d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 *
        (∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1))) *
          cubeForm ω U w w := by
  set f := cubeExtend ω U w
  set G : Vertex d → ℝ := fun x =>
    gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices (cubeCoarsen ω U w) x
  set g : Vertex d → ℝ := fun z => gradNormIn (openGraph ω) (crossingClusterVertices ω U) f z
  set a : Vertex d → ℝ := fun z => ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (d - 1)
  have hL := partition_sum_gradNormIn_coarseAnchor_rpow_le hd hP hU f (le_refl (1 : ℝ))
  have hexp : (1 : ℝ) * d - 1 = ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    ring
  simp only [Real.rpow_one, hexp, Real.rpow_natCast] at hL
  have hL' : ∑ x ∈ U.toIntegerCube.vertices, G x ≤
      coarseGradConstant d * ∑ z ∈ crossingClusterVertices ω U, a z * g z := hL
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (crossingClusterVertices ω U) a g
  have hg2 : ∑ z ∈ crossingClusterVertices ω U, g z ^ 2 = cubeForm ω U w w :=
    sum_gradNormIn_sq_eq_cubeForm w
  have ha2 : ∑ z ∈ crossingClusterVertices ω U, a z ^ 2 =
      ∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) :=
    Finset.sum_congr rfl fun z _ => by simp only [a]; rw [← pow_mul, mul_comm (d - 1) 2]
  have hG0 : 0 ≤ ∑ x ∈ U.toIntegerCube.vertices, G x :=
    Finset.sum_nonneg fun x _ => gradNormIn_nonneg _ _ _ _
  have hag0 : 0 ≤ ∑ z ∈ crossingClusterVertices ω U, a z * g z :=
    Finset.sum_nonneg fun z _ => mul_nonneg (by positivity) (gradNormIn_nonneg _ _ _ _)
  have hC := coarseGradConstant_nonneg d
  have hpair := abs_cubeCoarsePairing_le_sum_gradNormIn (ω := ω) q w
  have hq0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsq : √(2 * (d : ℝ)) ^ 2 = 2 * d := Real.sq_sqrt (by positivity)
  have h1 : |cubeCoarsePairing ω U q w| ≤ (∑ i, |q i|) * √(2 * (d : ℝ)) *
      (coarseGradConstant d * ∑ z ∈ crossingClusterVertices ω U, a z * g z) :=
    hpair.trans (mul_le_mul_of_nonneg_left hL' (by positivity))
  have h2 : cubeCoarsePairing ω U q w ^ 2 ≤ ((∑ i, |q i|) * √(2 * (d : ℝ)) *
      (coarseGradConstant d * ∑ z ∈ crossingClusterVertices ω U, a z * g z)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc cubeCoarsePairing ω U q w ^ 2
      ≤ ((∑ i, |q i|) * √(2 * (d : ℝ)) *
          (coarseGradConstant d * ∑ z ∈ crossingClusterVertices ω U, a z * g z)) ^ 2 := h2
    _ = (∑ i, |q i|) ^ 2 * √(2 * (d : ℝ)) ^ 2 * coarseGradConstant d ^ 2 *
          (∑ z ∈ crossingClusterVertices ω U, a z * g z) ^ 2 := by ring
    _ ≤ (∑ i, |q i|) ^ 2 * √(2 * (d : ℝ)) ^ 2 * coarseGradConstant d ^ 2 *
          ((∑ z ∈ crossingClusterVertices ω U, a z ^ 2) *
            ∑ z ∈ crossingClusterVertices ω U, g z ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by rw [hsq, ha2, hg2]; ring

/-- **Upper bound for `-μ`** (Armstrong and Dario, Lemma 4.4, (4.12)): on the partition event and
for a resolved cube, `-μ(U, q) ≤ d C₃² |q|₁² |U|⁻¹ ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{2d-2}`. -/
theorem neg_cubeMu_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) :
    -cubeMu ω U q ≤ d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 *
      (∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1))) /
        U.latticeVolume := by
  obtain ⟨u, -, -, hμ⟩ := exists_cubeMu_minimizer hd hP hU q
  have hvol := U.latticeVolume_pos
  set K2 := 2 * d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 *
    (∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)))
    with hK2
  have hK0 : 0 ≤ K2 := by positivity
  have hB := cubeForm_self_nonneg u
  have hsq := sq_cubeCoarsePairing_le hd hP hU q u
  rw [← hK2] at hsq
  set ℓ := cubeCoarsePairing ω U q u
  set B := cubeForm ω U u u
  have hℓ : ℓ ≤ (K2 + B) / 2 := by
    nlinarith [sq_nonneg (K2 - B), sq_nonneg (ℓ - (K2 + B) / 2)]
  rw [hμ, neg_div', div_le_div_iff_of_pos_right hvol]
  have e : d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 *
      (∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1))) =
      K2 / 2 := by
    rw [hK2]
    ring
  rw [e]
  linarith

/-- **Energy of the minimizer of `μ`** (Armstrong and Dario, (4.20)). -/
theorem cubeForm_cubeMu_minimizer_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) {u : CubeFun ω U} (hu : u ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u = cubeCoarsePairing ω U q w) :
    cubeForm ω U u u / U.latticeVolume ≤ 2 * d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 *
      (∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1))) /
        U.latticeVolume := by
  have h1 := cubeMu_mul_latticeVolume_eq hd hP hU q hu hvar
  have h2 := neg_cubeMu_le hd hP hU q
  have hvol := U.latticeVolume_pos
  rw [div_le_div_iff_of_pos_right hvol]
  rw [le_div_iff₀ hvol] at h2
  linarith

end Rigidity.Percolation
