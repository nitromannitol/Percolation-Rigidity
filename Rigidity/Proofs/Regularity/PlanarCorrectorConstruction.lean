import Rigidity.Proofs.Regularity.PlanarCorrectedPlaneExistence
import Rigidity.Proofs.Regularity.ClusterOrderOne

/-!
# The corrector of a slope from approximations on growing balls (AKM2, Proposition 3.1, Step 3)

Armstrong, Kuusi and Mourrat, *The additive structure of elliptic homogenization*
(arXiv:1602.00512v1), Proposition 3.1, Step 3, for `k = 1`, which Armstrong and Dario
(arXiv:1609.09431v2) follow for Theorem 2 (ii): from functions `v_m` harmonic on `𝒞 ∩ B_{3^m}` with
`‖v_m - q · x‖_{L̲²(B_{3^m})} ≤ A 3^m ε^m` (`ε = 3^{-δ}`) and the Lipschitz estimate at the origin,
the differences `w_m = v_{m+1} - v_m` are approximated by constants `c_m` on the balls `B_{3^j}`,
`j < m`, with error `C₀ 3^{j-m} ‖w_m‖`, and `v_n - Σ_{m<n} c_m - q · x` is at most `A' 3^j ε^j` on
`B_{3^j}` uniformly in `n ≥ j` (`telescoping_bound`). A subsequence converges at every vertex
(the space of functions on the countable cluster is sequentially compact on products of
intervals), and the limit is a harmonic function with the same bounds.

This file proves the telescoping bound and the passage to the limit; the input `v_m` is the
hypothesis `PlanarAffineApproximationTwo` of `PlanarCorrectorFromApproximation`.
-/

namespace Rigidity.Proofs.Regularity

open Finset Filter Topology LatticeProb LatticeProb.Percolation Rigidity.Percolation

variable {ω : Configuration 2}

/-- Harmonicity on the cluster of the ball `B_R` around the origin. -/
def HarmonicOnBall (C : OpenComponent ω) (v : C → ℝ) (R : ℝ) : Prop :=
  ∀ x ∈ componentEuclideanBall C 0 R,
    (∀ y : C, (componentGraph C).Adj x y → y ∈ componentEuclideanBall C 0 R) →
      componentLaplacian C v x = 0

theorem HarmonicOnBall.mono {C : OpenComponent ω} {v : C → ℝ} {R R' : ℝ}
    (h : HarmonicOnBall C v R') (hRR : R ≤ R') : HarmonicOnBall C v R := by
  intro x hx hy
  have hsub : ∀ z : C, z ∈ componentEuclideanBall C 0 R → z ∈ componentEuclideanBall C 0 R' := by
    intro z hz
    rw [mem_componentEuclideanBall] at hz ⊢
    linarith
  exact h x (hsub x hx) fun y hxy => hsub y (hy y hxy)

theorem HarmonicOnBall.sub {C : OpenComponent ω} {v v' : C → ℝ} {R : ℝ}
    (h : HarmonicOnBall C v R) (h' : HarmonicOnBall C v' R) : HarmonicOnBall C (v - v') R := by
  intro x hx hy
  rw [componentLaplacian_sub, h x hx hy, h' x hx hy, sub_zero]

theorem componentBallL2_zero (C : OpenComponent ω) (z : Vertex 2) (r : ℝ) :
    componentBallL2 C z r (fun _ => 0) = 0 := by
  unfold componentBallL2
  simp

theorem componentBallL2_sum_le (C : OpenComponent ω) (z : Vertex 2) (r : ℝ) (s : Finset ℕ)
    (g : ℕ → C → ℝ) :
    componentBallL2 C z r (fun x => ∑ m ∈ s, g m x) ≤ ∑ m ∈ s, componentBallL2 C z r (g m) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rw [componentBallL2_zero]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (Rigidity.Proofs.S2.componentBallL2_add_le C z r (g a) _).trans (by linarith)

theorem componentBallL2_const_le (C : OpenComponent ω) (z : Vertex 2) (r c : ℝ) :
    componentBallL2 C z r (fun _ => c) ≤ |c| :=
  componentBallL2_le_of_abs_le C z r (abs_nonneg c) fun _ _ => le_rfl

/-- **The telescoping bound** of Step 3: for `j ≥ m₀ + 1` and `n ≥ j`,
`‖v_n - Σ_{m₀ < m < n} c_m - ℓ‖_{L̲²(B_{3^j})} ≤ (A + C₂ + C₁/(1-ε) + C₃/(3ε-1)) 3^j ε^j`. -/
theorem telescoping_bound (C : OpenComponent ω) (ℓ : C → ℝ) (v : ℕ → C → ℝ) (c : ℕ → ℝ)
    {m₀ : ℕ} {A C₁ C₂ C₃ ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (h3ε : 1 < 3 * ε) (hC₁ : 0 ≤ C₁)
    (hC₃ : 0 ≤ C₃)
    (hv : ∀ m, m₀ ≤ m → componentBallL2 C 0 (3 ^ m) (fun x => v m x - ℓ x) ≤ A * 3 ^ m * ε ^ m)
    (hwc : ∀ m, m₀ + 1 ≤ m → ∀ j, m₀ ≤ j → j < m →
      componentBallL2 C 0 (3 ^ j) (fun x => v (m + 1) x - v m x - c m) ≤ C₁ * 3 ^ j * ε ^ m)
    (hwj : ∀ m, m₀ + 1 ≤ m →
      componentBallL2 C 0 (3 ^ m) (fun x => v (m + 1) x - v m x - c m) ≤ C₂ * 3 ^ m * ε ^ m)
    (hc : ∀ m, m₀ + 1 ≤ m → |c m| ≤ C₃ * 3 ^ m * ε ^ m)
    {j n : ℕ} (hj : m₀ + 1 ≤ j) (hjn : j ≤ n) :
    componentBallL2 C 0 (3 ^ j)
        (fun x => v n x - ∑ m ∈ Finset.Ico (m₀ + 1) n, c m - ℓ x) ≤
      (A + C₂ + C₁ / (1 - ε) + C₃ / (3 * ε - 1)) * 3 ^ j * ε ^ j := by
  have hdecomp : (fun x => v n x - ∑ m ∈ Finset.Ico (m₀ + 1) n, c m - ℓ x) =
      fun x => (v j x - ℓ x) + ((∑ m ∈ Finset.Ico j n, (v (m + 1) x - v m x - c m)) +
        ∑ m ∈ Finset.Ico (m₀ + 1) j, (-c m)) := by
    funext x
    have h1 : v n x = v j x + ∑ m ∈ Finset.Ico j n, (v (m + 1) x - v m x) := by
      have hs := Finset.sum_range_sub (fun k => v (j + k) x) (n - j)
      simp only [← add_assoc, add_zero] at hs
      rw [Finset.sum_Ico_eq_sum_range, hs, show j + (n - j) = n by omega]
      ring
    have h2 : ∑ m ∈ Finset.Ico (m₀ + 1) n, c m =
        ∑ m ∈ Finset.Ico (m₀ + 1) j, c m + ∑ m ∈ Finset.Ico j n, c m :=
      (Finset.sum_Ico_consecutive _ (by omega) hjn).symm
    rw [h1, h2]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  rw [hdecomp]
  have hs1 := Rigidity.Proofs.S2.componentBallL2_add_le C 0 (3 ^ j) (fun x => v j x - ℓ x)
    (fun x => (∑ m ∈ Finset.Ico j n, (v (m + 1) x - v m x - c m)) +
      ∑ m ∈ Finset.Ico (m₀ + 1) j, (-c m))
  have hs2 := Rigidity.Proofs.S2.componentBallL2_add_le C 0 (3 ^ j)
    (fun x => ∑ m ∈ Finset.Ico j n, (v (m + 1) x - v m x - c m))
    (fun _ => ∑ m ∈ Finset.Ico (m₀ + 1) j, (-c m))
  have hs3 := componentBallL2_sum_le C 0 (3 ^ j) (Finset.Ico j n)
    (fun m x => v (m + 1) x - v m x - c m)
  have hs4 := componentBallL2_const_le C 0 (3 ^ j) (∑ m ∈ Finset.Ico (m₀ + 1) j, (-c m))
  -- the sum over `m ≥ j`
  have hε0 : 0 < 1 - ε := by linarith
  have hsumw : ∑ m ∈ Finset.Ico j n,
      componentBallL2 C 0 (3 ^ j) (fun x => v (m + 1) x - v m x - c m) ≤
      (C₂ + C₁ / (1 - ε)) * 3 ^ j * ε ^ j := by
    have hpos2 : 0 ≤ C₁ / (1 - ε) * 3 ^ j * ε ^ j := by positivity
    rcases Nat.eq_or_lt_of_le hjn with h | h
    · rw [← h, Finset.Ico_self, Finset.sum_empty]
      have h0 := componentBallL2_nonneg C 0 (3 ^ j) (fun x => v (j + 1) x - v j x - c j)
      have h1 : 0 ≤ C₂ * 3 ^ j * ε ^ j := h0.trans (hwj j hj)
      nlinarith
    · rw [Finset.sum_eq_sum_Ico_succ_bot h]
      have htail : ∑ m ∈ Finset.Ico (j + 1) n,
          componentBallL2 C 0 (3 ^ j) (fun x => v (m + 1) x - v m x - c m) ≤
          C₁ / (1 - ε) * 3 ^ j * ε ^ j := by
        calc ∑ m ∈ Finset.Ico (j + 1) n,
              componentBallL2 C 0 (3 ^ j) (fun x => v (m + 1) x - v m x - c m)
            ≤ ∑ m ∈ Finset.Ico (j + 1) n, C₁ * 3 ^ j * ε ^ m :=
              Finset.sum_le_sum fun m hm => by
                obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hm
                exact hwc m (by omega) j (by omega) (by omega)
          _ = C₁ * 3 ^ j * ∑ m ∈ Finset.Ico (j + 1) n, ε ^ m := by rw [Finset.mul_sum]
          _ ≤ C₁ * 3 ^ j * (ε ^ (j + 1) / (1 - ε)) :=
              mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hε.le hε1) (by positivity)
          _ ≤ C₁ * 3 ^ j * (ε ^ j / (1 - ε)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hε.le hε1.le (by omega)) hε0.le
          _ = C₁ / (1 - ε) * 3 ^ j * ε ^ j := by ring
      have := hwj j hj
      linarith
  -- the constants of `m < j`
  have hsumc : |∑ m ∈ Finset.Ico (m₀ + 1) j, (-c m)| ≤ C₃ / (3 * ε - 1) * 3 ^ j * ε ^ j := by
    have h3 : 0 < 3 * ε - 1 := by linarith
    calc |∑ m ∈ Finset.Ico (m₀ + 1) j, (-c m)| ≤ ∑ m ∈ Finset.Ico (m₀ + 1) j, |-c m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ico (m₀ + 1) j, C₃ * (3 * ε) ^ m :=
          Finset.sum_le_sum fun m hm => by
            obtain ⟨h1, _⟩ := Finset.mem_Ico.1 hm
            rw [abs_neg, mul_pow]
            have := hc m h1
            linarith
      _ = C₃ * (((3 * ε) ^ j - (3 * ε) ^ (m₀ + 1)) / (3 * ε - 1)) := by
          rw [← Finset.mul_sum, geom_sum_Ico (by linarith) hj]
      _ ≤ C₃ * ((3 * ε) ^ j / (3 * ε - 1)) := by
          gcongr
          have : 0 ≤ (3 * ε) ^ (m₀ + 1) := by positivity
          linarith
      _ = C₃ / (3 * ε - 1) * 3 ^ j * ε ^ j := by rw [mul_pow]; ring
  calc _ ≤ componentBallL2 C 0 (3 ^ j) (fun x => v j x - ℓ x) +
        componentBallL2 C 0 (3 ^ j) (fun x =>
          (∑ m ∈ Finset.Ico j n, (v (m + 1) x - v m x - c m)) +
            ∑ m ∈ Finset.Ico (m₀ + 1) j, (-c m)) := hs1
    _ ≤ A * 3 ^ j * ε ^ j + ((C₂ + C₁ / (1 - ε)) * 3 ^ j * ε ^ j +
          C₃ / (3 * ε - 1) * 3 ^ j * ε ^ j) := by
        have h1 := hv j (by omega)
        have h2 := hs2.trans (add_le_add (hs3.trans hsumw) (hs4.trans hsumc))
        linarith
    _ = _ := by ring

end Rigidity.Proofs.Regularity
