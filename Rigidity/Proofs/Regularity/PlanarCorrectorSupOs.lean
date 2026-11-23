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

/-- **The uniform bound of the correctors above a minimal scale of class `O_s`**, from (1.18) in the
form `O_s`, the order-zero regularity and the minimal scales of Proposition 2.4. -/
theorem exists_corrector_sup_os (h118 : PlanarCorrectorSublinearL2Two)
    (hR3 : ArmstrongDarioOrderZeroTwo)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p) (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ s θ η Cs : ℝ, 0 < s ∧ 0 < θ ∧ 0 < η ∧ η ≤ 1 / 28 ∧ 0 ≤ Cs ∧
      ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin 2 → ℝ,
        ∃ u : uniqueInfiniteComponent h → ℝ, u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 ∧
          ∀ m : ℕ, X ω ≤ 3 ^ m → ∀ x : uniqueInfiniteComponent h, (∀ i, |x.val i| ≤ 9 * 3 ^ m) →
            |componentCorrector (uniqueInfiniteComponent h) q u x| ≤
              Cs * (|q 0| + |q 1|) * ((3 : ℝ) ^ m) ^ (1 - 7 * η) := by
  obtain ⟨s₁, δ₁, θ₁, K, hs₁, hδ₁, hθ₁, hK, X₁, hX₁m, -, hX₁os, hae₁⟩ := h118 p hpc hp1
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₁ 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hδ₁ one_pos
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
  have hδδ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hη : 0 < δ / 28 := by positivity
  have hη28 : δ / 28 ≤ 1 / 28 := by linarith
  obtain ⟨s₃, θ₃, C₀, hs₃, hθ₃, hC₀, Y, hYm, -, hYi, hYb, hae₃⟩ :=
    exists_planar_all_centres_constant_approximation hR3 p hpc hp1
  obtain ⟨rB, θB, hrB, hθB, XB, hXBm, -, hXBos, haeB⟩ :=
    exists_isOsBond_scale_le_three hs₃ hθ₃ hη hYm hYi hYb
  obtain ⟨A₀, sc, -, hmoms⟩ := hM5 p hpc hp1
  obtain ⟨K₆, r₆, θ₆, -, hr₆, hθ₆, M₆, hM₆m, -, hM₆os, hM₆ae⟩ := hmoms 1 one_pos (δ / 28) hη
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 54
  obtain ⟨M₄, hM₄m, -, hM₄os, hM₄ae⟩ := hcube 0
  obtain ⟨mc, hmc⟩ := exists_nat_ge (1 / (7 * (δ / 28)))
  -- the minimal scale
  obtain ⟨θa, hθa, ha⟩ := exists_isOsBond_max hs₁ hrB hθ₁ hθB hX₁m hXBm hX₁os hXBos
  obtain ⟨θb, hθb, hb⟩ := exists_isOsBond_max hr₆ hs₄ hθ₆ hθ₄ hM₆m hM₄m hM₆os hM₄os
  obtain ⟨θc, hθc, hc⟩ := exists_isOsBond_max (lt_min hs₁ hrB) (lt_min hr₆ hs₄) hθa hθb
    (hX₁m.max hXBm) (hM₆m.max hM₄m) ha hb
  set s := min (min s₁ rB) (min r₆ s₄) with hs
  have hs0 : 0 < s := lt_min (lt_min hs₁ hrB) (lt_min hr₆ hs₄)
  have hconst := isOsBond_const (d := 2) (p := p) (by positivity : (0 : ℝ) < 3 ^ (mc + 3)) hs0
  obtain ⟨θd, hθd, hd⟩ := exists_isOsBond_max hs0 hs0 hθc (by positivity)
    ((hX₁m.max hXBm).max (hM₆m.max hM₄m)) measurable_const hc hconst
  refine ⟨_, θd, δ / 28,
    3 * (729 ^ 2 * (196 * C₀ * (Real.sqrt (18225 / (theta 2 p / 2)) * (6 * K) + 1) + 1)) +
      9 * √(4050 * (6 * K) ^ 2 + 8 * 729 ^ 4 *
        (196 * C₀ * (Real.sqrt (18225 / (theta 2 p / 2)) * (6 * K) + 1) + 1) ^ 2),
    lt_min hs0 hs0, hθd, hη, hη28, by positivity,
    fun ω => max (max (max (X₁ ω) (XB ω)) (max (M₆ ω) (M₄ ω))) (3 ^ (mc + 3)),
    ((hX₁m.max hXBm).max (hM₆m.max hM₄m)).max measurable_const,
    fun ω => (by positivity : (0 : ℝ) ≤ 3 ^ (mc + 3)).trans (le_max_right _ _), hd, ?_⟩
  filter_upwards [hae₁, hae₃, haeB, hM₆ae, hM₄ae, ae_planarPartitionEvent hpc] with
    ω hω₁ hω₃ hωB hω₆ hω₄ hP
  intro h q
  obtain ⟨u, hu, hL2⟩ := hω₁ h q
  refine ⟨u, hu, fun m hm x hx => ?_⟩
  obtain ⟨-, hω₃'⟩ := hω₃
  have hR3ω := hω₃' h
  have hinf := uniqueInfiniteComponent_infinite h
  have hX₁ : X₁ ω ≤ 3 ^ m :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hm
  have hXB : XB ω ≤ 3 ^ m :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hm
  have hM₆ : M₆ ω ≤ 3 ^ m :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hm
  have hM₄ : M₄ ω ≤ 3 ^ m :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hm
  have hmc3 : mc + 3 ≤ m :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 ((le_max_right _ _).trans hm)
  have hYle : ∀ a ∈ triScaleBox (m + 1), Y a ω ≤ (3 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * (δ / 28)) :=
    fun a ha => hωB (m + 1) (hXB.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))) a ha
  have hM6 : M₆ ω ≤ 3 ^ (m + 4) := hM₆.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hsize := (hω₆ (m + 4) hM6).2.2.2.1
  have h6N : X₁ ω ≤ 6 * (9 * 3 ^ m) := by
    have : (0 : ℝ) ≤ 3 ^ m := by positivity
    linarith
  have hL2' : componentBallL2 (uniqueInfiniteComponent h) 0 (6 * (9 * 3 ^ m))
      (componentCorrector (uniqueInfiniteComponent h) q u) ≤
      K * (|q 0| + |q 1|) * (6 * (9 * 3 ^ m)) ^ (1 - δ) := by
    refine (hL2 _ h6N).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hN1 : (1 : ℝ) ≤ 6 * (9 * 3 ^ m) := by
      have : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      linarith
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  exact abs_corrector_le_of_minimalScales hP (uniqueInfiniteComponent h) hinf q u hu hδ0 hδ1 hmc
    hmc3 hK hC₀ (by positivity) (hω₄ h) hM₄ (fun a => Y a ω) hR3ω hYle hsize hL2' x hx

end Rigidity.Proofs.Regularity
