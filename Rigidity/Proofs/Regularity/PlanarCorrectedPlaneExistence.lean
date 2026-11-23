import Rigidity.Proofs.Regularity.PlanarCorrectorSupNorm

/-!
# The corrected planes of the planar cluster from the quantitative sublinearity in `L²`

`planarCorrectedPlaneExistenceTwo_of_sublinearL2` proves `PlanarCorrectedPlaneExistenceTwo` (every
slope has a corrected plane, sublinear in the uniform norm) from (1.18)
(`PlanarCorrectorSublinearL2Two`), the order-zero regularity of Theorem 2 (iii)
(`ArmstrongDarioOrderZeroTwo`) and the minimal scales of Proposition 2.4
(`PlanarMinimalScalesTwo`), by the argument of the Remark after (1.19) of Armstrong and Dario
(arXiv:1609.09431v2):

* the Lipschitz estimate at every centre (`exists_planar_all_centres_constant_approximation`) with
  the maximum of its minimal scales over the boxes (`ae_eventually_scale_le_three`) bounds the
  increments of the corrector;
* the uniform bound at each triadic scale (`abs_corrector_le_at_scale`), from the comparison with
  the coarsening and the interpolation inequality, gives (1.22);
* `componentSlopeAsymptotics_of_scales` turns it into the slope asymptotics.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

theorem eventually_le_three_pow (B : ℝ) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → B ≤ (3 : ℝ) ^ m := by
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 3)
  exact ⟨m₀, fun m hm => hm₀.le.trans (pow_le_pow_right₀ (by norm_num) hm)⟩

/-- **Every slope has a corrected plane on the planar cluster**, from (1.18), the order-zero
regularity and the minimal scales of Proposition 2.4. -/
theorem planarCorrectedPlaneExistenceTwo_of_sublinearL2 (h118 : PlanarCorrectorSublinearL2Two)
    (hR3 : ArmstrongDarioOrderZeroTwo)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p) :
    PlanarCorrectedPlaneExistenceTwo := by
  intro p hpc hp1
  obtain ⟨s₁, δ₁, θ₁, K, hs₁, hδ₁, hθ₁, hK, X₁, -, -, -, hae₁⟩ := h118 p hpc hp1
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₁ 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hδ₁ one_pos
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
  have hδδ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = δ / 28 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hη28 : η ≤ 1 / 28 := by rw [hηdef]; linarith
  obtain ⟨s₃, θ₃, C₀, hs₃, hθ₃, hC₀, Y, -, -, hYi, hYb, hae₃⟩ :=
    exists_planar_all_centres_constant_approximation hR3 p hpc hp1
  have hBC := ae_eventually_scale_le_three hs₃ hθ₃ hη hYi hYb
  obtain ⟨A₀, sc, -, hmoms⟩ := hM5 p hpc hp1
  obtain ⟨K₆, r₆, θ₆, -, -, -, M₆, -, -, -, hM₆ae⟩ := hmoms 1 one_pos η hη
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₄, θ₄, -, -, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 54
  obtain ⟨M₄, -, -, -, hM₄ae⟩ := hcube 0
  filter_upwards [hae₁, hae₃, hBC, hM₆ae, hM₄ae, ae_planarPartitionEvent hpc] with
    ω hω₁ hω₃ hωBC hω₆ hω₄ hP
  intro h q
  obtain ⟨u, hu, hL2⟩ := hω₁ h q
  refine ⟨u, hu, ?_⟩
  obtain ⟨-, hω₃'⟩ := hω₃
  have hR3ω := hω₃' h
  have hinf := uniqueInfiniteComponent_infinite h
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 hωBC
  have hκ : 0 < theta 2 p / 2 := by positivity
  -- the thresholds
  obtain ⟨ma, hma⟩ := eventually_le_three_pow (max (M₆ ω) (M₄ ω))
  obtain ⟨mb, hmb⟩ := eventually_le_three_pow (X₁ ω)
  obtain ⟨mc, hmc⟩ := exists_nat_ge (1 / (7 * η))
  set m₀ := max (max (max ma mb) (mc + 3)) k₀ with hm₀
  set K' : ℝ := 6 * K with hK'
  set CL : ℝ := 196 * C₀ * (Real.sqrt (18225 / (theta 2 p / 2)) * K' + 1) + 1 with hCL
  set qn : ℝ := |q 0| + |q 1| with hqn
  have hqn0 : 0 ≤ qn := by positivity
  refine componentSlopeAsymptotics_of_scales (uniqueInfiniteComponent h) q u (c₃ := 729 ^ 2 * CL * qn)
    (c₄ := √(4050 * K' ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * qn) hη hη28 (by positivity)
    (m₀ := m₀) fun m hm x hx => ?_
  have hma' : ma ≤ m := by omega
  have hmb' : mb ≤ m := by omega
  have hmc' : mc + 3 ≤ m := by omega
  have hk' : k₀ ≤ m + 1 := by omega
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
  have hL2' : componentBallL2 (uniqueInfiniteComponent h) 0 (6 * (9 * 3 ^ m)) (componentCorrector (uniqueInfiniteComponent h) q u) ≤
      K' * qn * (9 * 3 ^ m) / y ^ 28 := by
    have hX : X₁ ω ≤ 6 * (9 * 3 ^ m) := by
      have := hmb m hmb'
      have h3 : (0 : ℝ) ≤ 3 ^ m := by positivity
      linarith
    refine (hL2 _ hX).trans ?_
    have hN1 : (1 : ℝ) ≤ 6 * (9 * 3 ^ m) := by
      have : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      linarith
    have hpow1 : (6 * (9 * 3 ^ m) : ℝ) ^ (1 - δ₁) ≤ (6 * (9 * 3 ^ m)) ^ (1 - δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
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
    calc K * qn * (6 * (9 * 3 ^ m)) ^ (1 - δ₁) ≤ K * qn * (6 * (9 * 3 ^ m)) ^ (1 - δ) :=
          mul_le_mul_of_nonneg_left hpow1 (by positivity)
      _ = K * qn * (6 * (9 * 3 ^ m)) / (6 * (9 * 3 ^ m)) ^ δ := by rw [hpow2]; ring
      _ ≤ K * qn * (6 * (9 * 3 ^ m)) / y ^ 28 :=
          div_le_div_of_nonneg_left (by positivity) hy28 hpow3
      _ = K' * qn * (9 * 3 ^ m) / y ^ 28 := by rw [hK']; ring
  -- the minimal scales of the Lipschitz estimate
  have hYle : ∀ a : Vertex 2, (∀ i, |a i| ≤ 3 * (9 * 3 ^ m)) → Y a ω ≤ y := by
    intro a ha
    refine hk₀ (m + 1) hk' a (mem_triScaleBox.2 fun i => ?_)
    have := ha i
    have e : (3 : ℤ) * (9 * 3 ^ m) = 3 ^ (m + 1 + 2) := by ring
    rw [← e]; exact this
  -- the sizes of the partition cubes
  have hsize : ∀ z : Vertex 2, (∀ i, |z i| ≤ 2 * (9 * 3 ^ m)) →
      (3 : ℝ) ^ (planarPartCube ω z).scale ≤ 3 * y := by
    intro z hz
    have hM6 : M₆ ω ≤ 3 ^ (m + 4) := by
      have := hma m hma'
      have h1 : M₆ ω ≤ 3 ^ m := (le_max_left _ _).trans this
      have h2 : (3 : ℝ) ^ m ≤ 3 ^ (m + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hz' : z ∈ triadicCubeFinset 2 (m + 4) 0 := by
      rw [mem_square_iff_int]
      intro i
      have := hz i
      have h0 : (0 : ℤ) < 3 ^ m := by positivity
      have e : (3 : ℤ) ^ (m + 4) = 81 * 3 ^ m := by ring
      rw [e]; linarith
    have h := (hω₆ (m + 4) hM6).2.2.2.1 z (mem_cube_of_mem_square hz')
    refine h.trans ?_
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
  have hℓ : M₄ ω ≤ 3 ^ m := (le_max_right _ _).trans (hma m hma')
  have hmain := abs_corrector_le_at_scale hP (uniqueInfiniteComponent h) hinf q u hu (m := m) (y := y) (K := K')
    (C₀ := C₀) (κ := theta 2 p / 2) hy1 hy14 hyN (by positivity) hC₀.le hκ (hω₄ h) hℓ
    (fun a => Y a ω) (fun a _ R hR v hv => hR3ω a R hR v hv) hYle hsize hL2' x hx
  refine hmain.trans (le_of_eq ?_)
  rw [hCL, hqn]
  ring

/-- **The planar corrector input** (R2) from (1.18), the order-zero regularity, the minimal scales
of Proposition 2.4 and the bound `dim 𝒜_1 ≤ 3` of Theorem 2 (i). -/
theorem supercriticalBondCorrectorInputTwo_of_sublinearL2 (h118 : PlanarCorrectorSublinearL2Two)
    (hR3 : ArmstrongDarioOrderZeroTwo)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hdim : PlanarOrderOneDimensionTwo) : SupercriticalBondCorrectorInputTwo :=
  supercriticalBondCorrectorInputTwo_of_orderOne hR3
    (planarCorrectedPlaneExistenceTwo_of_sublinearL2 h118 hR3 hM5) hdim

end Rigidity.Proofs.Regularity
