import Rigidity.Frozen.MixedGreenEntryV1
import Rigidity.Support.MixedGreenMomentTransport
import Rigidity.Support.MixedGreenWorkingScale
import LatticeProb.Prob.Percolation.LatticeOrderZeroGradient
import LatticeProb.Prob.Percolation.GreenQuantitativeField
import LatticeProb.Prob.Percolation.GreenDifferenceBounds
import LatticeProb.Prob.Percolation.GreenColumnHarmonic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation LatticeProb.External
open scoped BigOperators Classical ENNReal

namespace Rigidity.Support

/-- The mixed Green estimate obtained from the cited value and regularity inputs. -/
theorem mixed_green : ∀ (_ : SupercriticalBondGreenQuantitative)
    (_ : ArmstrongDarioOrderZero)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ δ : ℝ, 0 < δ → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
      ∀ y : Vertex d, ∃ M : Configuration d → ℝ,
        Measurable M ∧ (∀ ω, 1 ≤ M ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (M ω / C) s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (Real.rpow (M ω / C) s) ∂latticeBondLaw d p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h : HasUniqueInfiniteOpenComponent ω,
              ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                ∀ g : uniqueInfiniteComponent h → uniqueInfiniteComponent h → ℝ,
                  (∀ z, IsGreenColumn d hd (uniqueInfiniteComponent h) z (g z)) →
                  ∀ x : uniqueInfiniteComponent h,
                    M ω ≤ (latticeL1Dist x.val y : ℝ) →
                    (∑ i : Fin d, ∑ j : Fin d,
                      |mixedEntry (uniqueInfiniteComponent h) g x ⟨y, hy⟩ i j|) ≤
                        C / Real.rpow (latticeL1Dist x.val y : ℝ) ((d : ℝ) - δ) := by
  intro hginput hreg d _ hd p hp hp1 δ hδ
  let δ₀ : ℝ := min δ (1 / 2)
  let η : ℝ := δ₀ / 4
  let α : ℝ := δ₀ / (2 * (d : ℝ))
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by linarith
  have hδ₀ : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδhalf : δ₀ ≤ 1 / 2 := min_le_right _ _
  have hδle : δ₀ ≤ δ := min_le_left _ _
  have hη : 0 < η := by dsimp [η]; positivity
  have hηd : η < (d : ℝ) - 1 := by dsimp [η]; linarith
  have hα : 0 < α := by dsimp [α]; positivity
  have hαhalf : α ≤ 1 / 2 := by
    dsimp [α]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  obtain ⟨sx, θ, K, hsx, hθ, hK, X, hXm, hXn, hXi, hXb, hgrad⟩ :=
    exists_all_centers_order_zero_gradient hreg d hd p hp hp1
  obtain ⟨κ, hκ, k, hkm, hgreen⟩ := exists_green_quantitative_field hginput d hd p hp hp1
  obtain ⟨Cg, sg, hCg, hsg, T, hTm, hTn, hTtail, hvalues⟩ := hgreen η hη
  obtain ⟨Cr, hCr, hrad⟩ := exists_neighbor_radial_scale_exp_moment (d := d)
    (Ω := Configuration d) θ sx Cg sg α hθ hsx hCg hsg hα
  obtain ⟨CF, hCF, hball⟩ :=
    exists_componentBallL2_green_difference_bound d hd ⟨κ, hκ⟩ Cg hCg
  let β : ℝ := α * min sx sg
  let B : ℝ := 4 * Real.sqrt K * CF
  let H : ℝ := (d : ℝ) ^ 2 * B * (d : ℝ) ^ d
  let C : ℝ := max ((d : ℝ) * Cr) (H + 1)
  have hβ : 0 < β := mul_pos hα (lt_min hsx hsg)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := lt_of_lt_of_le (mul_pos hdpos hCr) (le_max_left _ _)
  refine ⟨β, C, hβ, hC, ?_⟩
  intro y
  obtain ⟨Mr, hMr, hMr1, hMri, hMrb, hradial⟩ := hrad (latticeBondLaw d p) X T
    hXm hXn hXi hXb hTm hTn (fun z r hr => hTtail z r hr.le) y
  have hM := scaled_exp_moment_le (latticeBondLaw d p) Mr Cr C β (d : ℝ) hCr hC hβ
    (by linarith) (le_max_left _ _) hMr hMr1 hMri hMrb
  refine ⟨fun ω => (d : ℝ) * Mr ω, hM.1, hM.2.1, hM.2.2.1, hM.2.2.2, ?_⟩
  filter_upwards [hgrad, hvalues, hradial] with ω hgradω hvalueω hradω
  obtain ⟨huniq, hgradω⟩ := hgradω
  refine ⟨huniq, ?_⟩
  intro h hy g hg x hx
  let D : ℝ := ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖
  let L : ℝ := (latticeL1Dist x.val y : ℝ)
  let Ccomp := uniqueInfiniteComponent h
  let pole : Ccomp := ⟨y, hy⟩
  have hL : L ≤ (d : ℝ) * D := latticeL1Dist_le_dim_mul_euclidean x.val y
  change (d : ℝ) * Mr ω ≤ L at hx
  have hMrD : Mr ω ≤ D := by
    have h := mul_le_mul_of_nonneg_left hL (le_of_lt hdpos)
    nlinarith
  have hD1 : 1 ≤ D := (hMr1 ω).trans hMrD
  have hL1 : 1 ≤ L := by nlinarith [hMr1 ω]
  have hY := hradω x.val hMrD
  have hwork := neighbor_working_scale_bounds X T y x.val ω D α (norm_nonneg _) hα hαhalf hY
  have hlarge : 4096 < D := hwork.1
  have hmY : max 2 (X x.val ω) ≤ neighborRadialField X T y x.val ω := by
    apply max_le
    · have h64 : (64 : ℝ) ≤ neighborRadialField X T y x.val ω := le_max_left _ _
      linarith
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hmD : max 2 (X x.val ω) ≤ D ^ α := le_of_lt (lt_of_le_of_lt hmY hY)
  have hDpos : 0 < D := by linarith
  have hden : 0 < Real.rpow L ((d : ℝ) - δ) := Real.rpow_pos_of_pos (by linarith) _
  have hentry (i j : Fin d) : |Rigidity.mixedEntry Ccomp g x pole i j| ≤
      B * Real.rpow D (-(d : ℝ) + δ₀) := by
    by_cases hxe : (openGraph ω).Adj x.val (x.val + unit i)
    · by_cases hye : (openGraph ω).Adj y (y + unit j)
      · let xp : Ccomp := ⟨x.val + unit i, Ccomp.mem_supp_of_adj_mem_supp x.property hxe⟩
        let yp : Ccomp := ⟨y + unit j, Ccomp.mem_supp_of_adj_mem_supp hy hye⟩
        let F : Ccomp → ℝ := fun v => g pole v - g yp v - (k y ω - k (y + unit j) ω)
        have hsep := localization_poles_and_threshold Ccomp x.val y j pole yp rfl rfl
          (neighborMaximum T y ω) (by simpa only [dist_eq_norm] using hlarge)
          (by simpa only [dist_eq_norm] using hwork.2.2.1)
        have hharm := greenColumn_sub_sub_const_harmonic hd Ccomp pole yp (g pole) (g yp)
          (k y ω - k (y + unit j) ω) (hg pole) (hg yp) x.val (D / 4)
          (by simpa only [dist_eq_norm] using hsep.1)
          (by simpa only [dist_eq_norm] using hsep.2.1)
        have hgeo : ∀ v ∈ componentEuclideanBall Ccomp x.val (D / 4),
            D / 2 ≤ ‖latticeEuclideanEmbedding v.val - latticeEuclideanEmbedding y‖ ∧
            D / 2 ≤ ‖latticeEuclideanEmbedding v.val -
              latticeEuclideanEmbedding (y + unit j)‖ ∧
            ‖(latticeEuclideanEmbedding v.val - latticeEuclideanEmbedding y) -
              (latticeEuclideanEmbedding v.val -
                latticeEuclideanEmbedding (y + unit j))‖ ≤ 1 := by
          intro v hv
          have hv' := localization_ball_separation Ccomp x.val y j v
            (by simpa only [dist_eq_norm] using hlarge) (by simpa only [dist_eq_norm] using hv)
          have hunit := dist_embedding_add_unit y j
          rw [dist_eq_norm] at hunit
          have heq : (latticeEuclideanEmbedding v.val - latticeEuclideanEmbedding y) -
              (latticeEuclideanEmbedding v.val - latticeEuclideanEmbedding (y + unit j)) =
              latticeEuclideanEmbedding (y + unit j) - latticeEuclideanEmbedding y := by abel
          rw [heq, hunit]
          constructor
          · have h : 3 * D / 4 <
                ‖latticeEuclideanEmbedding v.val - latticeEuclideanEmbedding y‖ := by
              simpa only [dist_eq_norm] using hv'.1
            linarith
          · constructor
            · have h : D / 2 <
                  ‖latticeEuclideanEmbedding v.val -
                    latticeEuclideanEmbedding (y + unit j)‖ := by
                simpa only [dist_eq_norm] using hv'.2
              exact le_of_lt h
            · exact le_rfl
        have hgy : ∀ v ∈ componentEuclideanBall Ccomp x.val (D / 4),
            ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
              z.val = latticeEuclideanEmbedding v.val - latticeEuclideanEmbedding y →
              |g pole v - continuumGreen d hd ⟨κ, hκ⟩ z - k y ω| ≤
                Cg * Real.rpow ‖z.val‖ (1 - d + η) := by
          intro v hv z hz
          apply hvalueω y h hy (g pole) (hg pole) v z hz
          have ht := (hsep.2.2 v (by simpa only [dist_eq_norm] using hv)).1
          rw [dist_eq_norm, ← hz] at ht
          exact (le_neighborMaximum_self T y ω).trans (le_of_lt ht)
        have hgyp : ∀ v ∈ componentEuclideanBall Ccomp x.val (D / 4),
            ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
              z.val = latticeEuclideanEmbedding v.val - latticeEuclideanEmbedding (y + unit j) →
              |g yp v - continuumGreen d hd ⟨κ, hκ⟩ z - k (y + unit j) ω| ≤
                Cg * Real.rpow ‖z.val‖ (1 - d + η) := by
          intro v hv z hz
          apply hvalueω (y + unit j) h yp.property (g yp) (hg yp) v z hz
          have ht := (hsep.2.2 v (by simpa only [dist_eq_norm] using hv)).2
          rw [dist_eq_norm, ← hz] at ht
          exact (le_neighborMaximum_neighbor T y j ω).trans (le_of_lt ht)
        have hnorm := hball η hη hηd D hD1 Ccomp x.val y (y + unit j) (D / 4)
          (g pole) (g yp) (k y ω) (k (y + unit j) ω) hgeo hgy hgyp
        have hadj : (componentGraph Ccomp).Adj x xp := hxe
        have hsq := hgradω h x (D / 4) hwork.2.2.2 F
          (fun v hv _ => hharm v hv) xp hadj
        have hdecay := abs_le_of_squared_gradient_bound d hd δ hδ D
          (max 2 (X x.val ω)) K CF (componentBallL2 Ccomp x.val (D / 4) F) (F x - F xp)
          hD1 (by positivity) (by simpa [α, δ₀] using hmD) hK hCF
          (componentBallL2_nonneg Ccomp x.val (D / 4) F) (by simpa [F, η, δ₀] using hnorm)
          (by simpa [F] using hsq)
        have heq : Rigidity.mixedEntry Ccomp g x pole i j = F x - F xp := by
          simp only [pole, Rigidity.mixedEntry, dif_pos hxe, dif_pos hye]
          dsimp [F, xp, yp, pole]
          ring
        rw [heq]
        simpa only [B, δ₀] using hdecay
      · simp only [pole, Rigidity.mixedEntry, dif_pos hxe, dif_neg hye, abs_zero]
        exact mul_nonneg hB.le (le_of_lt (Real.rpow_pos_of_pos hDpos _))
    · simp only [pole, Rigidity.mixedEntry, dif_neg hxe, abs_zero]
      exact mul_nonneg hB.le (le_of_lt (Real.rpow_pos_of_pos hDpos _))
  have hsum : (∑ i : Fin d, ∑ j : Fin d, |Rigidity.mixedEntry Ccomp g x pole i j|) ≤
      (d : ℝ) ^ 2 * B * Real.rpow D (-(d : ℝ) + δ₀) := by
    calc
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, B * Real.rpow D (-(d : ℝ) + δ₀) := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have htransfer := decay_rpow_le_lattice d hd δ₀ δ D L hδ₀ hδhalf hδle hDpos hL1 hL
  calc
    _ ≤ (d : ℝ) ^ 2 * B * Real.rpow D (-(d : ℝ) + δ₀) := hsum
    _ ≤ (d : ℝ) ^ 2 * B * ((d : ℝ) ^ d / Real.rpow L ((d : ℝ) - δ)) := by gcongr
    _ = H / Real.rpow L ((d : ℝ) - δ) := by dsimp [H]; ring
    _ ≤ C / Real.rpow L ((d : ℝ) - δ) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact le_trans (by linarith : H ≤ H + 1) (le_max_right _ _)

end Rigidity.Support
