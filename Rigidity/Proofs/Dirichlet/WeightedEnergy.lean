import Rigidity.Proofs.Dirichlet.HardyDirectional
import Rigidity.Proofs.Dirichlet.SecondDifferences

/-!
# A weighted energy estimate for the discrete Dirichlet problem

For constant diagonal conductances `a_k > 0`, a weight `W > 0` whose gradient ratios satisfy
`R_k(x) + R_k(x − e_k) ≤ κ Δ_k W(x)` on `U` with `κ ≤ 1/4`, and `u = f + φ` harmonic on `U` with
`φ = 0` off `U`, the weighted energies `X = Σ a_k W̄_k (∇_k φ)²` and `Y = Σ a_k W̄_k (∇_k f)²`
satisfy `X ≤ 11 Y`: test the equation with `φ W`, use the identity
`∇(φW) ∇φ = W̄ (∇φ)² + ½ ∇W ∇(φ²)`, summation by parts for the second term, the directional
Hardy inequality and Young's inequality.

With the two-sided power-type weights `W ≃ dist(x, ∂□)^{-γ}`, this is the weighted estimate that
gives the smallness of the energy of the homogenized solution in a boundary layer, in place of
the global Meyers estimate in the proof of Armstrong–Dario, Lemma 6.3, Step 3.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The edge identity `(B P' − A P)(B − A) = ½ (P + P') (B − A)² + ½ (P' − P)(B² − A²)`. -/
theorem edge_product_identity (A B P P' : ℝ) :
    (B * P' - A * P) * (B - A) =
      (P + P') / 2 * (B - A) ^ 2 + 1 / 2 * ((P' - P) * (B ^ 2 - A ^ 2)) := by
  ring

/-- The pointwise bound of the data term: with `m = (P + P')/2`,
`−(B P' − A P) F ≤ ¼ m (B − A)² + (9/2) m F² + ½ A² (P' − P)²/m` for `P, P' > 0`. -/
theorem neg_edge_data_le {A B P P' F : ℝ} (hP : 0 < P) (hP' : 0 < P') :
    -((B * P' - A * P) * F) ≤ 1 / 4 * ((P + P') / 2 * (B - A) ^ 2) +
      9 / 2 * ((P + P') / 2 * F ^ 2) + 1 / 2 * (A ^ 2 * ((P' - P) ^ 2 / ((P + P') / 2))) := by
  set m := (P + P') / 2 with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hPm : P' ≤ 2 * m := by rw [hm]; linarith
  -- the gradient part
  have b1 : -(P' * (B - A) * F) ≤ 1 / 4 * (m * (B - A) ^ 2) + 4 * (m * F ^ 2) := by
    by_cases huv : 0 ≤ (B - A) * F
    · have : 0 ≤ P' * ((B - A) * F) := mul_nonneg hP'.le huv
      nlinarith [sq_nonneg (B - A), sq_nonneg F, hm0]
    · push Not at huv
      have h1 : -(P' * (B - A) * F) ≤ -(2 * m * ((B - A) * F)) := by
        nlinarith
      nlinarith [mul_nonneg hm0.le (sq_nonneg ((B - A) / 2 + 2 * F))]
  -- the weight part
  have b2 : -(A * (P' - P) * F) ≤ 1 / 2 * (A ^ 2 * ((P' - P) ^ 2 / m)) + 1 / 2 * (m * F ^ 2) := by
    rw [← sub_nonneg]
    have h : 1 / 2 * (A ^ 2 * ((P' - P) ^ 2 / m)) + 1 / 2 * (m * F ^ 2) -
        -(A * (P' - P) * F) = (A * (P' - P) + m * F) ^ 2 / (2 * m) := by
      field_simp
      ring
    rw [h]
    positivity
  have hsplit : -((B * P' - A * P) * F) = -(P' * (B - A) * F) + -(A * (P' - P) * F) := by ring
  rw [hsplit]
  linarith

end Rigidity.Dirichlet
