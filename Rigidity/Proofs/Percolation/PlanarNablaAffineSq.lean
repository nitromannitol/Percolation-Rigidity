import Rigidity.Proofs.Percolation.PlanarFlatnessTools
import Rigidity.Proofs.Percolation.PlanarNuLowerBound
import Rigidity.Proofs.Percolation.PlanarReachMoments
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeBounds

/-!
# The spatial average of the coarsened gradient of `v(·, □, p)` in `L²(P)`

For a resolved cube `V` of side `L` on the partition event, the spatial average of the coarsened
gradient of the maximizer `v` of `ν(V, p)` differs from `p` by the boundary error (planar form of
Lemma 4.8 of Armstrong and Dario), whence the pointwise bound

`∑_j (|V|⁻¹ ⟨e_j, ∇[v]_P⟩_V - p_j)² ≤ C |p|² (L⁻² ∑_{x ∈ ∂V} s_x⁸ + L⁻¹)`,

`s_x` the side of the partition cube of `x`. Off the partition event or for an unresolved cube,
`v = 0` and the left side is `|p|²`, which is at most `|p|² ∑_{x ∈ V} (s_x / 3 L)⁶` on the
partition event. The right sides are measurable and, the moments of `s_x` being bounded,

`E[∑_j (|V|⁻¹ ⟨e_j, ∇[v(·, V, p)]_P⟩_V - p_j)²] ≤ C |p|² 3^{-n/4}`

for every cube `V` of scale `n`: display (4.26) of Armstrong and Dario in `L²`, in dimension two,
with the rate `3^{-n/4}` used in the proof of Lemma 5.8 (the proof gives `3^{-n}`).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The side of the partition cube of a vertex on the partition event, and zero otherwise. -/
noncomputable def partSideP (ω : Configuration 2) (x : Vertex 2) : ℝ :=
  if PlanarPartitionEvent ω then partSide ω x else 0

theorem partSideP_nonneg (ω : Configuration 2) (x : Vertex 2) : 0 ≤ partSideP ω x := by
  unfold partSideP
  split_ifs
  · exact le_trans zero_le_one (one_le_partSide x)
  · exact le_rfl

theorem measurable_partSideP (x : Vertex 2) : Measurable fun ω => partSideP ω x := by
  let φ : Configuration 2 → Option (TriadicCube 2) := fun ω =>
    if PlanarPartitionEvent ω then some (planarPartCube ω x) else none
  refine measurable_of_fiber_const φ (fun t => ?_) (fun ω ω' h => ?_)
  · rcases t with _ | Q
    · have heq : φ ⁻¹' {none} = {ω | PlanarPartitionEvent ω}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h <;> simp [h]
      rw [heq]
      exact measurableSet_planarPartitionEvent.compl
    · have heq : φ ⁻¹' {some Q} = {ω | PlanarPartitionEvent ω} ∩
          {ω | x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarGoodCubes ω)} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h
        · simp only [Option.some.injEq, h, true_and]
          constructor
          · rintro rfl
            exact planarPartCube_spec h x
          · rintro ⟨hx, hQ⟩
            exact planarPartCube_eq h hx hQ
        · simp [h]
      rw [heq]
      exact measurableSet_planarPartitionEvent.inter (measurableSet_setOf.2
        (measurable_const.and (measurable_isMaximalStopping_planarGoodCubes Q)))
  · simp only [partSideP]
    by_cases h1 : PlanarPartitionEvent ω <;> by_cases h2 : PlanarPartitionEvent ω'
    · simp only [φ, if_pos h1, if_pos h2, Option.some.injEq] at h
      rw [if_pos h1, if_pos h2, partSide, partSide, h]
    · simp [φ, h1, h2] at h
    · simp [φ, h1, h2] at h
    · rw [if_neg h1, if_neg h2]

/-- The square of a finite sum is at most the number of terms times the sum of squares. -/
theorem sq_sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- `(a + b)² ≤ 2 a² + 2 b²`. -/
theorem add_sq_le_two_mul (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The algebra of the pointwise bound. -/
theorem nablaAffine_algebra {Q P₁ L S S8 Y : ℝ} (hQ : 0 ≤ Q) (hP₁Q : P₁ ^ 2 ≤ 2 * Q)
    (hL1 : 1 ≤ L) (hS8 : 0 ≤ S8) (hSS : S ^ 2 ≤ 4 * L * S8)
    (hY2 : Y ^ 2 ≤ 2 * (162001 ^ 2 * S ^ 2 / (L * L * L)) + 2 * (1 / (4 * L))) :
    4 * (9 * P₁ * Y) ^ 2 + 2 * (Q / (L * L)) ≤
      1296 * 162001 ^ 2 * Q * (4 * (S8 / (L * L)) + 1 / L) := by
  have hL0 : 0 < L := by linarith
  set a := S8 / (L * L) with ha
  set b := 1 / L with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hSa : S ^ 2 / (L * L * L) ≤ 4 * a := by
    rw [ha, div_le_iff₀ (by positivity)]
    have e : 4 * (S8 / (L * L)) * (L * L * L) = 4 * L * S8 := by field_simp
    rw [e]
    exact hSS
  have h4L : 1 / (4 * L) = b / 4 := by rw [hb]; field_simp
  have hLL : Q / (L * L) ≤ Q * b := by
    rw [hb, div_le_iff₀ (by positivity)]
    have e : Q * (1 / L) * (L * L) = Q * L := by field_simp
    rw [e]
    nlinarith
  have hYb : Y ^ 2 ≤ 2 * (162001 ^ 2 * (4 * a)) + b / 2 := by
    have : 162001 ^ 2 * S ^ 2 / (L * L * L) = 162001 ^ 2 * (S ^ 2 / (L * L * L)) := by ring
    rw [this, h4L] at hY2
    nlinarith
  have hPY : P₁ ^ 2 * Y ^ 2 ≤ 2 * Q * (2 * (162001 ^ 2 * (4 * a)) + b / 2) :=
    mul_le_mul hP₁Q hYb (sq_nonneg Y) (by positivity)
  have e : (9 * P₁ * Y) ^ 2 = 81 * (P₁ ^ 2 * Y ^ 2) := by ring
  rw [e]
  nlinarith [mul_nonneg hQ hb0, mul_nonneg hQ ha0]

/-- `|v(·, V, p)|` at the trivial slope: the coarse pairings vanish. -/
theorem planarNuGradAvg_eq_zero_of_eq_zero (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (j : Fin 2) : planarNuGradAvg ω V 0 j = 0 := by
  have hsol : planarNuSolution ω V 0 = planarNuMaximizer ω V 0 := by
    rw [planarNuSolution, if_pos ⟨hP, hV⟩]
  obtain ⟨hvA, hvar⟩ := planarNuMaximizer_spec (ω := ω) V 0
  have hB : clusterForm ω V (planarNuMaximizer ω V 0) (planarNuMaximizer ω V 0) = 0 := by
    rw [hvar _ hvA, fluxPairing_apply]
    simp
  rw [planarNuGradAvg, hsol, coarsePairing_eq_zero_of_clusterForm hP hV _ hB, zero_div]

/-- The bound in each direction, through the boundary error. -/
theorem planarNuGradAvg_sub_sq_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (p : Fin 2 → ℝ) (hp : 0 < |p 0| + |p 1|) (j : Fin 2) :
    (planarNuGradAvg ω V p j - p j) ^ 2 ≤
      2 * (9 * (|p 0| + |p 1|) * (162001 * (∑ k ∈ boundaryIndex V, partSide ω k.2.2 ^ 4) /
          ((V.toIntegerCube.size : ℝ) * Real.sqrt (V.toIntegerCube.size : ℝ)) +
        1 / 2 / Real.sqrt (V.toIntegerCube.size : ℝ))) ^ 2 +
      2 * (p j ^ 2 / ((V.toIntegerCube.size : ℝ) * (V.toIntegerCube.size : ℝ))) := by
  set L : ℝ := (V.toIntegerCube.size : ℝ) with hL
  have hL1 : 1 ≤ L := one_le_cast_size V
  have hL0 : 0 < L := by linarith
  have hLvol : L * L = V.volume := cast_size_mul_self V
  set v := planarNuMaximizer ω V p with hv
  have hsol : planarNuSolution ω V p = v := by
    rw [planarNuSolution, if_pos ⟨hP, hV⟩]
  obtain ⟨hvA, hvar⟩ := planarNuMaximizer_spec (ω := ω) V p
  rw [← hv] at hvA hvar
  set P₁ := |p 0| + |p 1| with hP₁
  set Y := 162001 * (∑ k ∈ boundaryIndex V, partSide ω k.2.2 ^ 4) / (L * Real.sqrt L) +
    1 / 2 / Real.sqrt L with hY
  set E := boundaryError ω V p v with hE
  have hEb : P₁ * E / V.volume ≤ 9 * P₁ ^ 2 * Y := mul_boundaryError_div_le hP hV p hvA hvar
  have hEY : E / V.volume ≤ 9 * P₁ * Y := by
    have h1 : P₁ * (E / V.volume) ≤ P₁ * (9 * P₁ * Y) := by
      have e1 : P₁ * (E / V.volume) = P₁ * E / V.volume := by ring
      have e2 : P₁ * (9 * P₁ * Y) = 9 * P₁ ^ 2 * Y := by ring
      rw [e1, e2]
      exact hEb
    exact le_of_mul_le_mul_left h1 hp
  obtain ⟨c, hc⟩ := exists_affine_boundary_of_variation hP hV p hvar
  have hb := abs_coarsePairing_sub_le hP hV p (Pi.single j 1) hc
  have hsj : ∑ i, (Pi.single j 1 : Fin 2 → ℝ) i * p i = p j := by
    fin_cases j <;> simp [Fin.sum_univ_two]
  have hnj : |(Pi.single j 1 : Fin 2 → ℝ) 0| + |(Pi.single j 1 : Fin 2 → ℝ) 1| = 1 := by
    fin_cases j <;> simp
  rw [hsj, hnj, one_mul] at hb
  set ℓ := coarsePairing ω V (Pi.single j 1) v with hℓ
  have hgrad : planarNuGradAvg ω V p j = ℓ / V.volume := by
    rw [planarNuGradAvg, hsol]
  have e : planarNuGradAvg ω V p j - p j =
      (ℓ - p j * (L * (L - 1))) / V.volume + (-(p j / L)) := by
    rw [hgrad, ← hLvol]
    field_simp
    ring
  rw [e]
  have h1 : |(ℓ - p j * (L * (L - 1))) / V.volume| ≤ 9 * P₁ * Y := by
    rw [abs_div, abs_of_pos V.volume_pos]
    exact (div_le_div_of_nonneg_right hb V.volume_pos.le).trans hEY
  have h2 : ((ℓ - p j * (L * (L - 1))) / V.volume) ^ 2 ≤ (9 * P₁ * Y) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (-(p j / L)) ^ 2 = p j ^ 2 / (L * L) := by
    rw [neg_sq, div_pow, sq L]
  have h4 := add_sq_le_two_mul ((ℓ - p j * (L * (L - 1))) / V.volume) (-(p j / L))
  rw [h3] at h4
  linarith

/-- **The spatial average of the coarsened gradient of `v`, pointwise.** -/
theorem sum_sq_planarNuGradAvg_sub_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (p : Fin 2 → ℝ) :
    ∑ j : Fin 2, (planarNuGradAvg ω V p j - p j) ^ 2 ≤
      1296 * 162001 ^ 2 * (p 0 ^ 2 + p 1 ^ 2) *
        (4 * ((∑ k ∈ boundaryIndex V, partSide ω k.2.2 ^ 8) /
            ((V.toIntegerCube.size : ℝ) * (V.toIntegerCube.size : ℝ))) +
          1 / (V.toIntegerCube.size : ℝ)) := by
  set L : ℝ := (V.toIntegerCube.size : ℝ) with hL
  have hL1 : 1 ≤ L := one_le_cast_size V
  have hL0 : 0 < L := by linarith
  set S := ∑ k ∈ boundaryIndex V, partSide ω k.2.2 ^ 4 with hS
  set S8 := ∑ k ∈ boundaryIndex V, partSide ω k.2.2 ^ 8 with hS8
  have hS80 : 0 ≤ S8 := Finset.sum_nonneg fun k _ => by positivity
  have hQ0 : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := by positivity
  rcases eq_or_lt_of_le (show 0 ≤ |p 0| + |p 1| by positivity) with hz | hpos
  · have hp0 : p = 0 := by
      funext i
      have h0 : |p 0| = 0 := by linarith [abs_nonneg (p 0), abs_nonneg (p 1)]
      have h1 : |p 1| = 0 := by linarith [abs_nonneg (p 0), abs_nonneg (p 1)]
      fin_cases i
      · exact abs_eq_zero.1 h0
      · exact abs_eq_zero.1 h1
    subst hp0
    rw [Fin.sum_univ_two, planarNuGradAvg_eq_zero_of_eq_zero hP hV,
      planarNuGradAvg_eq_zero_of_eq_zero hP hV]
    simp
  set Y := 162001 * S / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L with hY
  have hj := planarNuGradAvg_sub_sq_le hP hV p hpos
  rw [← hL, ← hS, ← hY] at hj
  have hsqL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hsq0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hY2 : Y ^ 2 ≤ 2 * (162001 ^ 2 * S ^ 2 / (L * L * L)) + 2 * (1 / (4 * L)) := by
    have h1 : Y ^ 2 ≤ 2 * (162001 * S / (L * Real.sqrt L)) ^ 2 +
        2 * (1 / 2 / Real.sqrt L) ^ 2 := by
      rw [hY]
      exact add_sq_le_two_mul _ _
    have e1 : (162001 * S / (L * Real.sqrt L)) ^ 2 = 162001 ^ 2 * S ^ 2 / (L * L * L) := by
      rw [div_pow, mul_pow, mul_pow, hsqL]
      ring
    have e2 : (1 / 2 / Real.sqrt L) ^ 2 = 1 / (4 * L) := by
      rw [div_pow, div_pow, hsqL]
      ring
    rw [e1, e2] at h1
    exact h1
  have hSS : S ^ 2 ≤ 4 * L * S8 := by
    have h1 := sq_sum_le_card_mul (boundaryIndex V) fun k => partSide ω k.2.2 ^ 4
    have h2 := card_boundaryIndex_le V
    rw [← hS] at h1
    rw [← hL] at h2
    have e : ∑ k ∈ boundaryIndex V, (partSide ω k.2.2 ^ 4) ^ 2 = S8 := by
      rw [hS8]
      exact Finset.sum_congr rfl fun k _ => by rw [← pow_mul]
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hS80)
  have hsum : ∑ j : Fin 2, (planarNuGradAvg ω V p j - p j) ^ 2 ≤
      4 * (9 * (|p 0| + |p 1|) * Y) ^ 2 + 2 * ((p 0 ^ 2 + p 1 ^ 2) / (L * L)) := by
    rw [Fin.sum_univ_two]
    have h0 := hj 0
    have h1 := hj 1
    have e : p 0 ^ 2 / (L * L) + p 1 ^ 2 / (L * L) = (p 0 ^ 2 + p 1 ^ 2) / (L * L) := by ring
    linarith
  exact hsum.trans (nablaAffine_algebra hQ0 (abs_add_abs_sq_le p) hL1 hS80 hSS hY2)

end Rigidity.Percolation
