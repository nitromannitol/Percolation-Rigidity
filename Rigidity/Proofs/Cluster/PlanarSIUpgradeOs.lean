import Rigidity.Proofs.Cluster.PlanarSubaddOsMain

/-!
# Lemma 5.11 of Armstrong and Dario in dimension two, in the form `O_s`

`ω(V, q) = ν(V, ā⁻¹ q) - μ(V, q) - q · ā⁻¹ q` is the difference of the two error forms of
Proposition 5.2, `ω(V, q) = f_ν(ā⁻¹ q) - f_μ(q)` (`planarOmega_eq_sub`), so
`sup_q |q|⁻² |ω(V, q)| ≤ (1 + 2 S²) X(V) ≤ O_r(C 3^{-α scale V})` (`planar_SIupgrade_os`,
Lemma 5.11 of the source as printed). The source proves Lemma 5.11 first and derives
Proposition 5.2 from it; here the order is reversed, both from the tail bounds of
`PlanarSubaddTail.lean`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

theorem planarAhom_mulVec_inv_mulVec {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (q : Fin 2 → ℝ) : planarAhom p *ᵥ ((planarAhom p)⁻¹ *ᵥ q) = q := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (planarAhom_det_ne_zero hpc)),
    Matrix.one_mulVec]

/-- `ω(V, q) = f_ν(ā⁻¹ q) - f_μ(q)`. -/
theorem planarOmega_eq_sub {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (ω : Configuration 2) (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    planarOmega p ω V q = planarNuErr p ω V ((planarAhom p)⁻¹ *ᵥ q) - planarMuErr p ω V q := by
  have hdot : ∑ i, ((planarAhom p)⁻¹ *ᵥ q) i * (planarAhom p *ᵥ ((planarAhom p)⁻¹ *ᵥ q)) i =
      ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
    rw [planarAhom_mulVec_inv_mulVec hpc]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  unfold planarOmega planarNuErr planarMuErr
  rw [hdot]
  split_ifs <;> ring

/-- **Armstrong and Dario, Lemma 5.11** (dimension two, `p > p_c(2)`):
`sup_q |q|⁻² |ω(V, q)| ≤ O_r(C 3^{-α scale V})` for every triadic cube `V`, with a measurable
majorant. -/
theorem planar_SIupgrade_os {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ r α C : ℝ, 0 < r ∧ 0 < α ∧ 0 < C ∧ ∀ V : TriadicCube 2,
      ∃ Z : Configuration 2 → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond 2 p Z r (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
        ∀ (ω : Configuration 2) (q : Fin 2 → ℝ),
          |planarOmega p ω V q| ≤ Z ω * (q 0 ^ 2 + q 1 ^ 2) := by
  obtain ⟨r, α, C, hr, hα, hC, hV⟩ := planar_subadd_os hpc
  obtain ⟨S, hS0, hS⟩ := exists_abs_mulVec_le (planarAhom p)⁻¹
  refine ⟨r, α, (1 + 2 * S ^ 2) * C, hr, hα, by positivity, fun V => ?_⟩
  obtain ⟨hm, h0, hos, hb⟩ := hV V
  refine ⟨fun ω => (1 + 2 * S ^ 2) * planarSubaddErr p V ω, hm.const_mul _,
    fun ω => mul_nonneg (by positivity) (h0 ω), ?_, fun ω q => ?_⟩
  · have := Rigidity.Proofs.S2.IsOsBond.const_mul (by positivity : (0 : ℝ) < 1 + 2 * S ^ 2) hos
    simpa only [mul_assoc] using this
  · obtain ⟨hμ, hν⟩ := hb ω q ((planarAhom p)⁻¹ *ᵥ q)
    rw [planarOmega_eq_sub hpc]
    set w := (planarAhom p)⁻¹ *ᵥ q with hw
    have hw2 : w 0 ^ 2 + w 1 ^ 2 ≤ 2 * S ^ 2 * (q 0 ^ 2 + q 1 ^ 2) := by
      have h1 : w 0 ^ 2 + w 1 ^ 2 ≤ (|w 0| + |w 1|) ^ 2 := by
        rw [← sq_abs (w 0), ← sq_abs (w 1)]
        nlinarith only [abs_nonneg (w 0), abs_nonneg (w 1)]
      have h2 := pow_le_pow_left₀ (by positivity) (hS q) 2
      have h3 := mul_le_mul_of_nonneg_left (l1_sq_le_two_mul q) (sq_nonneg S)
      calc w 0 ^ 2 + w 1 ^ 2 ≤ _ := h1
        _ ≤ (S * (|q 0| + |q 1|)) ^ 2 := h2
        _ = S ^ 2 * (|q 0| + |q 1|) ^ 2 := by ring
        _ ≤ S ^ 2 * (2 * (q 0 ^ 2 + q 1 ^ 2)) := h3
        _ = _ := by ring
    have hX0 := h0 ω
    calc |planarNuErr p ω V w - planarMuErr p ω V q|
        ≤ |planarNuErr p ω V w| + |planarMuErr p ω V q| := abs_sub _ _
      _ ≤ planarSubaddErr p V ω * (w 0 ^ 2 + w 1 ^ 2) +
          planarSubaddErr p V ω * (q 0 ^ 2 + q 1 ^ 2) := add_le_add hν hμ
      _ ≤ planarSubaddErr p V ω * (2 * S ^ 2 * (q 0 ^ 2 + q 1 ^ 2)) +
          planarSubaddErr p V ω * (q 0 ^ 2 + q 1 ^ 2) := by
          gcongr
      _ = (1 + 2 * S ^ 2) * planarSubaddErr p V ω * (q 0 ^ 2 + q 1 ^ 2) := by ring

/-- **The upper bound (4.13) of `-μ`, in the form `O_s`** (Armstrong and Dario, `e.muupboundwhip`,
dimension two, with the rate `size^{-α}` of Proposition 5.2 in place of `size^{-1}`):
`-μ(V, q) ≤ (K + Z(V)) |q|²` with `Z(V) ≤ O_r(C 3^{-α scale V})`, `μ` set to `0` off the event. -/
theorem planar_muupbound_os {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ r α C K : ℝ, 0 < r ∧ 0 < α ∧ 0 < C ∧ 0 ≤ K ∧ ∀ V : TriadicCube 2,
      ∃ Z : Configuration 2 → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond 2 p Z r (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
        ∀ (ω : Configuration 2) (q : Fin 2 → ℝ),
          (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V q else 0) ≤
            (K + Z ω) * (q 0 ^ 2 + q 1 ^ 2) := by
  obtain ⟨r, α, C, hr, hα, hC, hV⟩ := planar_subadd_os hpc
  obtain ⟨S, hS0, hS⟩ := exists_abs_mulVec_le (planarAhom p)⁻¹
  refine ⟨r, α, C, S, hr, hα, hC, hS0, fun V => ?_⟩
  obtain ⟨hm, h0, hos, hb⟩ := hV V
  refine ⟨planarSubaddErr p V, hm, h0, hos, fun ω q => ?_⟩
  have hμ := (hb ω q q).1
  have hdot : 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i ≤ S * (q 0 ^ 2 + q 1 ^ 2) := by
    have h1 := abs_dotProduct_le q ((planarAhom p)⁻¹ *ᵥ q)
    have h2 := mul_le_mul_of_nonneg_left (hS q) (show 0 ≤ |q 0| + |q 1| by positivity)
    have h3 := mul_le_mul_of_nonneg_left (l1_sq_le_two_mul q) hS0
    have h4 := le_abs_self (∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i)
    nlinarith only [h1, h2, h3, h4]
  have e : (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V q else 0) =
      -(if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarMu ω V q else 0) := by
    split_ifs <;> simp
  rw [e]
  unfold planarMuErr at hμ
  set I := if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarMu ω V q else 0 with hI
  set d := 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i with hd
  have h6 : -(I + d) ≤ planarSubaddErr p V ω * (q 0 ^ 2 + q 1 ^ 2) := (neg_le_abs _).trans hμ
  calc -I ≤ planarSubaddErr p V ω * (q 0 ^ 2 + q 1 ^ 2) + d := by linarith
    _ ≤ planarSubaddErr p V ω * (q 0 ^ 2 + q 1 ^ 2) + S * (q 0 ^ 2 + q 1 ^ 2) := by linarith
    _ = (S + planarSubaddErr p V ω) * (q 0 ^ 2 + q 1 ^ 2) := by ring

end Rigidity.Proofs.Cluster
