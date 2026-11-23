import Rigidity.Proofs.Regularity.PlanarLocalScalesOs
import Rigidity.Proofs.Regularity.PlanarCorrectedPlaneExistence
import Rigidity.Proofs.Regularity.PlanarAffineApproximationOs

/-!
# The sup-norm bound of the correctors with a minimal scale of class `O_s`

The Remark after (1.19) of Armstrong and Dario (arXiv:1609.09431v2) upgrades (1.18) to the
uniform bound on the balls: at a scale `N = 9 · 3^m` above the minimal scales, the Lipschitz
estimate of order zero at the vertices of the box of side `6N`, the coarse graining and the bound
(1.18) on `B_{6N}` give `|χ(x)| ≤ C |q|₁ (3^m)^{1 - 7η}` on the box of side `2N`
(`abs_corrector_le_at_scale`). With the local scales of the Lipschitz estimate collected over the
boxes into a minimal scale of class `O_s` (`exists_isOsBond_scale_le_three`) and (1.18) in the form
`O_s`, all the minimal scales are of class `O_s` (`exists_corrector_sup_os`).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

/-- The two terms of the uniform bound at the scale `9 · 3^m` with `y = 3^{(m+1)η}`. -/
theorem scale_terms_simplify {m : ℕ} {η c₃ c₄ : ℝ} (hη : 0 < η) (hη28 : η ≤ 1 / 28)
    (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) :
    c₃ * ((3 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * η)) ^ 7 +
        c₄ * (9 * 3 ^ m) / ((3 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * η)) ^ 7 ≤
      (3 * c₃ + 9 * c₄) * ((3 : ℝ) ^ m) ^ (1 - 7 * η) := by
  have e1 : ((3 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * η)) ^ 7 = (3 : ℝ) ^ (7 * η * ((m : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf
  have e2 : ((3 : ℝ) ^ m) ^ (1 - 7 * η) = (3 : ℝ) ^ ((m : ℝ) * (1 - 7 * η)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [e1, e2]
  have hA : (3 : ℝ) ^ (7 * η * ((m : ℝ) + 1)) ≤ 3 * (3 : ℝ) ^ ((m : ℝ) * (1 - 7 * η)) := by
    rw [show (3 : ℝ) * (3 : ℝ) ^ ((m : ℝ) * (1 - 7 * η)) = (3 : ℝ) ^ (1 + (m : ℝ) * (1 - 7 * η)) by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hB : 9 * 3 ^ m / (3 : ℝ) ^ (7 * η * ((m : ℝ) + 1)) ≤
      9 * (3 : ℝ) ^ ((m : ℝ) * (1 - 7 * η)) := by
    rw [div_le_iff₀ (by positivity), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast (3 : ℝ) m]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hA hc₃
  have h2 : c₄ * (9 * 3 ^ m) / (3 : ℝ) ^ (7 * η * ((m : ℝ) + 1)) ≤
      c₄ * (9 * (3 : ℝ) ^ ((m : ℝ) * (1 - 7 * η))) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hB hc₄
  nlinarith

/-- **The uniform bound of the corrector at the scale `9 · 3^m`** above the minimal scales, for
one configuration (the argument of `planarCorrectedPlaneExistenceTwo_of_sublinearL2Ae`). -/
theorem abs_corrector_le_of_minimalScales {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (C : OpenComponent ω) (hinf : C.supp.Infinite) (q : Fin 2 → ℝ) (u : C → ℝ)
    (hu : u ∈ harmonicGrowthSpace C 1) {m mc : ℕ} {δ K C₀ κ ℓ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hmc : 1 / (7 * (δ / 28)) ≤ mc) (hm : mc + 3 ≤ m) (hK : 0 ≤ K)
    (hC₀ : 0 < C₀) (hκ : 0 < κ) (hcube : ClusterCubeDensity C 0 54 ℓ κ) (hℓ : ℓ ≤ 3 ^ m)
    (Yv : Vertex 2 → ℝ)
    (hR3 : ∀ a : Vertex 2, ∀ (R : ℝ), 2 * Yv a ≤ R → ∀ v : C → ℝ,
      (∀ x ∈ componentEuclideanBall C a R,
        (∀ z : C, (componentGraph C).Adj x z → z ∈ componentEuclideanBall C a R) →
          componentLaplacian C v x = 0) →
      ∃ c : ℝ, ∀ r : ℝ, Yv a ≤ r → r ≤ R / 2 →
        componentBallL2 C a r (v - fun _ => c) ≤ C₀ * (r / R) * componentBallL2 C a R v)
    (hYle : ∀ a ∈ triScaleBox (m + 1), Yv a ≤ (3 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * (δ / 28)))
    (hsize : ∀ x ∈ Rigidity.Proofs.Cluster.cube (m + 4) (0 : Vertex 2),
      (3 : ℝ) ^ (planarPartCube ω x).scale ≤ ((3 : ℝ) ^ (m + 4)) ^ (δ / 28))
    (hL2 : componentBallL2 C 0 (6 * (9 * 3 ^ m)) (componentCorrector C q u) ≤
      K * (|q 0| + |q 1|) * (6 * (9 * 3 ^ m)) ^ (1 - δ))
    (x : C) (hx : ∀ i, |x.val i| ≤ 9 * 3 ^ m) :
    |componentCorrector C q u x| ≤
      (3 * (729 ^ 2 * (196 * C₀ * (Real.sqrt (18225 / κ) * (6 * K) + 1) + 1)) +
        9 * √(4050 * (6 * K) ^ 2 + 8 * 729 ^ 4 *
          (196 * C₀ * (Real.sqrt (18225 / κ) * (6 * K) + 1) + 1) ^ 2)) *
        (|q 0| + |q 1|) * ((3 : ℝ) ^ m) ^ (1 - 7 * (δ / 28)) := by
  set η : ℝ := δ / 28 with hηdef
  have hη : 0 < η := by positivity
  have hη28 : η ≤ 1 / 28 := by rw [hηdef]; linarith
  set K' : ℝ := 6 * K with hK'
  set CL : ℝ := 196 * C₀ * (Real.sqrt (18225 / κ) * K' + 1) + 1 with hCL
  set qn : ℝ := |q 0| + |q 1| with hqn
  have hqn0 : 0 ≤ qn := by positivity
  set y : ℝ := (3 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * η) with hy
  have hypow : ∀ k : ℕ, y ^ k = (3 : ℝ) ^ (k * ((((m + 1 : ℕ) : ℝ)) * η)) := fun k => by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
  have hy1 : 1 ≤ y := Real.one_le_rpow (by norm_num) (by positivity)
  have hy14 : 2 ≤ y ^ 14 := by
    rw [hypow]
    refine le_trans ?_ (le_three_rpow (by positivity))
    have hm1 : (mc : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by
      have : mc + 1 ≤ m + 1 := by omega
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)] at hmc
    have h7 := mul_le_mul_of_nonneg_right hm1 (by positivity : (0 : ℝ) ≤ 7 * η)
    calc (2 : ℝ) ≤ 2 * ((mc : ℝ) * (7 * η)) := by linarith
      _ ≤ 2 * (((mc : ℝ) + 1) * (7 * η)) := by linarith
      _ ≤ 2 * (((m + 1 : ℕ) : ℝ) * (7 * η)) := by linarith
      _ = ((14 : ℕ) : ℝ) * ((((m + 1 : ℕ) : ℝ)) * η) := by push_cast; ring
  have hyN : 30 * y ≤ 9 * 3 ^ m := by
    have h1 : y ≤ (3 : ℝ) ^ ((((m + 1 : ℕ) : ℝ)) / 28) := by
      rw [hy]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hη28 (by positivity)
    have h2 : (3 : ℝ) ^ ((((m + 1 : ℕ) : ℝ)) / 28) * 81 ≤ 9 * 3 ^ m := by
      have e1 : (3 : ℝ) ^ ((((m + 1 : ℕ) : ℝ)) / 28) * 81 =
          (3 : ℝ) ^ ((((m + 1 : ℕ) : ℝ)) / 28 + 4) := by
        rw [Real.rpow_add (by norm_num)]; norm_num
      have e2 : (9 : ℝ) * 3 ^ m = (3 : ℝ) ^ (((m : ℕ) : ℝ) + 2) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; norm_num; ring
      rw [e1, e2]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
      push_cast
      linarith
    linarith
  -- (1.18) at `6N`
  have hL2' : componentBallL2 C 0 (6 * (9 * 3 ^ m)) (componentCorrector C q u) ≤
      K' * qn * (9 * 3 ^ m) / y ^ 28 := by
    refine hL2.trans ?_
    have hpow2 : (6 * (9 * 3 ^ m) : ℝ) ^ (1 - δ) = 6 * (9 * 3 ^ m) / (6 * (9 * 3 ^ m)) ^ δ := by
      rw [Real.rpow_sub (by positivity), Real.rpow_one]
    have hpow3 : y ^ 28 ≤ (6 * (9 * 3 ^ m) : ℝ) ^ δ := by
      rw [hypow]
      have e : (3 : ℝ) ^ ((28 : ℕ) * ((((m + 1 : ℕ) : ℝ)) * η)) =
          ((3 : ℝ) ^ (m + 1)) ^ δ := by
        rw [← Real.rpow_natCast (3 : ℝ) (m + 1), ← Real.rpow_mul (by norm_num), hηdef]
        congr 1
        push_cast
        ring
      rw [e]
      apply Real.rpow_le_rpow (by positivity) _ hδ0.le
      have : (0 : ℝ) ≤ 3 ^ m := by positivity
      rw [pow_succ]
      linarith
    have hy28 : 0 < y ^ 28 := by positivity
    calc K * qn * (6 * (9 * 3 ^ m)) ^ (1 - δ)
        = K * qn * (6 * (9 * 3 ^ m)) / (6 * (9 * 3 ^ m)) ^ δ := by rw [hpow2]; ring
      _ ≤ K * qn * (6 * (9 * 3 ^ m)) / y ^ 28 :=
          div_le_div_of_nonneg_left (by positivity) hy28 hpow3
      _ = K' * qn * (9 * 3 ^ m) / y ^ 28 := by rw [hK']; ring
  have hYle' : ∀ a : Vertex 2, (∀ i, |a i| ≤ 3 * (9 * 3 ^ m)) → Yv a ≤ y := by
    intro a ha
    refine hYle a (mem_triScaleBox.2 fun i => ?_)
    have := ha i
    have e : (3 : ℤ) * (9 * 3 ^ m) = 3 ^ (m + 1 + 2) := by ring
    rw [← e]; exact this
  have hsize' : ∀ z : Vertex 2, (∀ i, |z i| ≤ 2 * (9 * 3 ^ m)) →
      (3 : ℝ) ^ (planarPartCube ω z).scale ≤ 3 * y := by
    intro z hz
    have hz' : z ∈ triadicCubeFinset 2 (m + 4) 0 := by
      rw [mem_square_iff_int]
      intro i
      have := hz i
      have h0 : (0 : ℤ) < 3 ^ m := by positivity
      have e : (3 : ℤ) ^ (m + 4) = 81 * 3 ^ m := by ring
      rw [e]; linarith
    refine (hsize z (mem_cube_of_mem_square hz')).trans ?_
    have e : ((3 : ℝ) ^ (m + 4)) ^ η = (3 : ℝ) ^ (3 * η) * y := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    rw [e]
    have h3 : (3 : ℝ) ^ (3 * η) ≤ 3 := by
      calc (3 : ℝ) ^ (3 * η) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 3 := Real.rpow_one 3
    exact mul_le_mul_of_nonneg_right h3 (by linarith)
  have hmain := abs_corrector_le_at_scale hP C hinf q u hu (m := m) (y := y) (K := K')
    (C₀ := C₀) (κ := κ) hy1 hy14 hyN (by positivity) hC₀.le hκ hcube hℓ
    Yv (fun a _ R hR v hv => hR3 a R hR v hv) hYle' hsize' hL2' x hx
  refine hmain.trans ?_
  have hs := scale_terms_simplify (m := m) (η := η) hη hη28 (c₃ := 729 ^ 2 * CL * qn)
    (c₄ := √(4050 * K' ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * qn) (by positivity) (by positivity)
  calc _ = 729 ^ 2 * CL * qn * y ^ 7 + √(4050 * K' ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * qn *
        (9 * 3 ^ m) / y ^ 7 := by ring
    _ ≤ _ := hs
    _ = _ := by ring

end Rigidity.Proofs.Regularity
