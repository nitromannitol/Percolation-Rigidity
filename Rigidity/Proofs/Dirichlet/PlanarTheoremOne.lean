import Rigidity.Proofs.Dirichlet.PlanarChainBound
import Rigidity.Proofs.Cluster.PlanarAhomIsotropic
import Rigidity.Proofs.S2.ScaleInputsFaithful

/-!
# Theorem 1 of Armstrong and Dario in dimension two

From the convergence of `μ` and `ν` on the mesoscopic triadic cubes (`PlanarMesoscopicConvergence`)
and the minimal scales of the planar partition (`PlanarMinimalScales`), Theorem 1 of Armstrong and
Dario holds in dimension two with the discrete homogenized solution, for every exponent `p' > 2`
(`planarHomogenizationError_of_inputs`). The homogenized solution is
`u_hom = dirichletSolution (σ) (interior of □_m) w̃`, `w̃ = planarDatum`, with `ā = σ I`
(`exists_planarAhom_eq_smul_one`). The proof takes `t = (2 + p')/2`, `γ = min(1/16, (t − 2)/(2t))`,
`k = ⌈m/8⌉`, `c₀ = min(8α, 1/2, 4(1 − 2/t), 4γ)`, `k₀ = ⌊c₀ (m + 1)/192⌋` (from the minimal scales
with the exponent `384/c₀`), applies `planar_error_chain` and `chain_le`, and gives the rate
`α' = c₀/32`; the random scale is the maximum of `𝒩`, the five minimal scales and `3^11`.
-/

open MeasureTheory Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.Section5
open scoped Matrix Classical

namespace Rigidity.Dirichlet

/-- The maximum of two random scales of bounded `O_s` norms has a bounded `O_s` norm. -/
theorem exists_isOsBond_max {p : unitInterval} {X Y : Configuration 2 → ℝ} {s s' θ θ' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hθ : 0 < θ) (hθ' : 0 < θ') (hX : Measurable X)
    (hY : Measurable Y) (h : IsOsBond 2 p X s θ) (h' : IsOsBond 2 p Y s' θ') :
    ∃ θ'' : ℝ, 0 < θ'' ∧ IsOsBond 2 p (fun ω => max (X ω) (Y ω)) (min s s') θ'' :=
  ⟨_, by positivity, Rigidity.Proofs.S2.IsOsBond.max (lt_min hs hs') (by positivity)
    (by positivity) hX hY
    (Rigidity.Proofs.S2.IsOsBond.mono_exponent (lt_min hs hs') (min_le_left _ _) hX h)
    (Rigidity.Proofs.S2.IsOsBond.mono_exponent (lt_min hs hs') (min_le_right _ _) hY h')⟩

theorem smul_one_mulVec_two (σ : ℝ) (ξ : Fin 2 → ℝ) :
    1 / 2 * ∑ i, ξ i * ((σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ξ) i =
      σ * (∑ j, ξ j ^ 2) / 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  ring

theorem inv_smul_one_two {σ : ℝ} (hσ : σ ≠ 0) :
    (σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = σ⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, inv_mul_cancel₀ hσ,
      one_smul])

theorem smul_one_inv_mulVec_two {σ : ℝ} (hσ : σ ≠ 0) (q : Fin 2 → ℝ) :
    1 / 2 * ∑ i, q i * ((σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ *ᵥ q) i =
      (∑ j, q j ^ 2 / σ) / 2 := by
  rw [inv_smul_one_two hσ]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  ring

theorem planarDatumConst_nonneg {s p' CM : ℝ} (hCM : 0 ≤ CM) : 0 ≤ planarDatumConst s p' CM := by
  have := planarConstThree_nonneg
  have := planarConstTwo_nonneg
  unfold planarDatumConst
  positivity

theorem planarGradNorm_nonneg (ω : Configuration 2) (m : ℕ) (p' : ℝ) (u : Vertex 2 → ℝ) :
    0 ≤ planarGradNorm ω m p' u :=
  Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) (by positivity)) _

theorem chainBound_nonneg {σ E γ t A2 At K₀ C₃ CA : ℝ} (hσ : 0 < σ)
    (hγt : γ * (t / (t - 2)) < 1) (hE : 0 ≤ E) (hA2 : 0 ≤ A2) (hAt : 0 ≤ At) (hK₀ : 0 ≤ K₀)
    (hC₃ : 0 ≤ C₃) (hCA : 0 ≤ CA) : 0 ≤ chainBound σ E γ t A2 At K₀ C₃ CA := by
  have h1 := chainBoundOne_nonneg hσ hE hA2 hAt (t := t)
  have h2 := chainBoundTwo_nonneg hσ hγt hE hA2 hAt hK₀ hCA
  unfold chainBound
  positivity

/-- The rate of the error chain in `m`. -/
theorem three_pow_rate_le {c₀ : ℝ} (hc₀ : 0 < c₀) {m k k₀ : ℕ} (hmk : m ≤ 8 * k)
    (hk₀ : (k₀ : ℝ) ≤ c₀ / 192 * (m + 1)) :
    ((3 : ℝ) ^ k₀) ^ 12 * ((3 : ℝ) ^ k) ^ (-c₀) ≤
      3 ^ (c₀ / 16) * ((3 : ℝ) ^ (-(c₀ / 32 * m))) ^ 2 := by
  have hL12 : ((3 : ℝ) ^ k₀) ^ 12 = (3 : ℝ) ^ ((k₀ : ℝ) * 12) := by
    rw [← pow_mul, ← Real.rpow_natCast, Nat.cast_mul]
    norm_num
  have hKc : ((3 : ℝ) ^ k) ^ (-c₀) = (3 : ℝ) ^ ((k : ℝ) * -c₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hR : ((3 : ℝ) ^ (-(c₀ / 32 * m))) ^ 2 = (3 : ℝ) ^ (-(c₀ / 32 * m) * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hL12, hKc, hR, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hmk' : (m : ℝ) ≤ 8 * k := by exact_mod_cast hmk
  have := mul_le_mul_of_nonneg_left hmk' hc₀.le
  nlinarith

/-- **Armstrong and Dario, Theorem 1, in dimension two, with the discrete homogenized solution**,
from the convergence of `μ` and `ν` on the mesoscopic cubes and the minimal scales of the planar
partition. -/
theorem planarHomogenizationError_of_inputs {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hconv : PlanarMesoscopicConvergence p)
    (hms : PlanarMinimalScales p) {p' : ℝ} (hp' : 2 < p') : PlanarHomogenizationError p p' := by
  obtain ⟨σ, hσ, hA⟩ := exists_planarAhom_eq_smul_one hpc
  obtain ⟨sN, αc, Cc, hsN, hαc, hCc, N, hNm, -, hNos, hNae⟩ := hconv
  -- the exponents
  obtain ⟨t, ht, htp⟩ : ∃ t : ℝ, 2 < t ∧ t < p' := ⟨(2 + p') / 2, by linarith, by linarith⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨γ, hγ0, hγ, hγt⟩ : ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 / 16 ∧ γ * (t / (t - 2)) < 1 := by
    refine ⟨min (1 / 16) ((t - 2) / (2 * t)), lt_min (by norm_num)
      (div_pos (by linarith) (by linarith)), min_le_left _ _, ?_⟩
    have ht2 : t - 2 ≠ 0 := by linarith
    have h3 : (t - 2) / (2 * t) * (t / (t - 2)) = 1 / 2 := by
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero ht0.ne') ht2)]
      ring
    calc min (1 / 16) ((t - 2) / (2 * t)) * (t / (t - 2)) ≤ (t - 2) / (2 * t) * (t / (t - 2)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (div_nonneg (by linarith) (by linarith))
      _ = 1 / 2 := h3
      _ < 1 := by norm_num
  obtain ⟨c₀, hc₀0, hc₀α, hc₀h, hc₀t, hc₀γ⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 8 * αc ∧ c₀ ≤ 1 / 2 ∧
      c₀ ≤ 4 * (1 - 2 / t) ∧ c₀ ≤ 4 * γ := by
    have h2t : 2 / t < 1 := (div_lt_one ht0).2 ht
    exact ⟨min (8 * αc) (min (1 / 2) (min (4 * (1 - 2 / t)) (4 * γ))),
      lt_min (by linarith) (lt_min (by norm_num) (lt_min (by linarith) (by linarith))),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  -- the minimal scales: four moment bounds and the bound on the sizes
  have hq2 : 0 < p' - 2 := by linarith
  have hqt : 0 < p' - t := by linarith
  obtain ⟨s1, C1, hs1, hC1, M1, hM1m, -, hM1os, hM1ae⟩ :=
    hms ((2 * ((2 : ℕ) : ℝ) - 1) * (p' / (p' - 2)) + 2) (by
      have : 0 ≤ (2 * ((2 : ℕ) : ℝ) - 1) * (p' / (p' - 2)) :=
        mul_nonneg (by norm_num) (div_nonneg (by linarith) hq2.le)
      linarith)
  obtain ⟨s2, C2, hs2, hC2, M2, hM2m, -, hM2os, hM2ae⟩ :=
    hms ((2 * ((2 : ℕ) : ℝ)) * (p' / (p' - 2)) + 2) (by
      have : 0 ≤ (2 * ((2 : ℕ) : ℝ)) * (p' / (p' - 2)) :=
        mul_nonneg (by norm_num) (div_nonneg (by linarith) hq2.le)
      linarith)
  obtain ⟨s3, C3, hs3, hC3, M3, hM3m, -, hM3os, hM3ae⟩ :=
    hms ((t * ((2 : ℕ) : ℝ) - 1) * (p' / (p' - t)) + 2) (by
      have : 0 ≤ (t * ((2 : ℕ) : ℝ) - 1) * (p' / (p' - t)) :=
        mul_nonneg (by push_cast; linarith) (div_nonneg (by linarith) hqt.le)
      linarith)
  obtain ⟨s4, C4, hs4, hC4, M4, hM4m, -, hM4os, hM4ae⟩ :=
    hms ((t * ((2 : ℕ) : ℝ)) * (p' / (p' - t)) + 2) (by
      have : 0 ≤ (t * ((2 : ℕ) : ℝ)) * (p' / (p' - t)) :=
        mul_nonneg (by push_cast; linarith) (div_nonneg (by linarith) hqt.le)
      linarith)
  obtain ⟨s5, C5, hs5, hC5, M5, hM5m, -, hM5os, hM5ae⟩ :=
    hms (384 / c₀) (by rw [le_div_iff₀ hc₀0]; linarith)
  -- the error chain and its constants
  obtain ⟨K₀, C₃, CA, hK₀0, hC₃, hCA, hchain⟩ := planar_error_chain hσ
  set CM := max (max C1 C2) (max C3 C4)
  have hCM0 : 0 ≤ CM := hC1.le.trans ((le_max_left _ _).trans (le_max_left _ _))
  set A2 := planarDatumConst 2 p' CM
  set At := planarDatumConst t p' CM
  have hA20 : 0 ≤ A2 := planarDatumConst_nonneg hCM0
  have hAt0 : 0 ≤ At := planarDatumConst_nonneg hCM0
  set E := Cc * (3 : ℝ) ^ (7 * αc) with hEdef
  have hE0 : 0 ≤ E := by positivity
  set B := chainBound σ E γ t A2 At K₀ C₃ CA
  have hB0 : 0 ≤ B := chainBound_nonneg hσ hγt hE0 hA20 hAt0 hK₀0 hC₃ hCA
  -- the random scale
  have hmeas := ((((hNm.max hM1m).max hM2m).max hM3m).max hM4m).max hM5m
  obtain ⟨θ1, hθ1, hos1⟩ := exists_isOsBond_max hsN hs1 hCc hC1 hNm hM1m hNos hM1os
  obtain ⟨θ2, hθ2, hos2⟩ := exists_isOsBond_max (lt_min hsN hs1) hs2 hθ1 hC2 (hNm.max hM1m) hM2m
    hos1 hM2os
  obtain ⟨θ3, hθ3, hos3⟩ := exists_isOsBond_max (lt_min (lt_min hsN hs1) hs2) hs3 hθ2 hC3
    ((hNm.max hM1m).max hM2m) hM3m hos2 hM3os
  obtain ⟨θ4, hθ4, hos4⟩ := exists_isOsBond_max (lt_min (lt_min (lt_min hsN hs1) hs2) hs3) hs4
    hθ3 hC4 (((hNm.max hM1m).max hM2m).max hM3m) hM4m hos3 hM4os
  obtain ⟨θ5, hθ5, hos5⟩ := exists_isOsBond_max
    (lt_min (lt_min (lt_min (lt_min hsN hs1) hs2) hs3) hs4) hs5 hθ4 hC5
    ((((hNm.max hM1m).max hM2m).max hM3m).max hM4m) hM5m hos4 hM5os
  obtain ⟨θ6, hθ6, hos6⟩ := exists_isOsBond_max
    (lt_min (lt_min (lt_min (lt_min (lt_min hsN hs1) hs2) hs3) hs4) hs5) one_pos hθ5
    (by positivity : (0 : ℝ) < 3 ^ 11 * 3 ^ (1 / (1 : ℝ))) hmeas measurable_const hos5
    (Rigidity.Proofs.S2.isOsBond_const (d := 2) (p := p) (by positivity : (0 : ℝ) < 3 ^ 11)
      one_pos)
  set sX := min (min (min (min (min (min sN s1) s2) s3) s4) s5) 1
  have hsX0 : 0 < sX :=
    lt_min (lt_min (lt_min (lt_min (lt_min (lt_min hsN hs1) hs2) hs3) hs4) hs5) one_pos
  set Cf := max (max A2 √(B * 3 ^ (c₀ / 16))) θ6
  have hCf0 : 0 < Cf := lt_of_lt_of_le hθ6 (le_max_right _ _)
  refine ⟨sX, c₀ / 32, Cf, σ, hsX0, by positivity, hCf0, hσ, hA,
    fun ω => max (max (max (max (max (max (N ω) (M1 ω)) (M2 ω)) (M3 ω)) (M4 ω)) (M5 ω)) (3 ^ 11),
    hmeas.max measurable_const, fun ω => le_max_of_le_right (by positivity),
    Rigidity.Proofs.S2.IsOsBond.mono_scale hsX0 hθ6 (le_max_right _ _)
      (hmeas.max measurable_const) hos6, ?_⟩
  filter_upwards [ae_planarPartitionEvent hpc, hNae, hM1ae, hM2ae, hM3ae, hM4ae, hM5ae] with
    ω hP hN h1 h2 h3 h4 h5
  intro m hXm
  simp only [max_le_iff] at hXm
  obtain ⟨⟨⟨⟨⟨⟨hNm', h1m⟩, h2m⟩, h3m⟩, h4m⟩, h5m⟩, h11⟩ := hXm
  have hm11 : 11 ≤ m := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h11
  set k := (m + 7) / 8
  have h8k : 8 * k ≤ m + 7 := by omega
  have hmk : m ≤ 8 * k := by omega
  -- the scale `k₀` of the partition cubes of `□_{m+1}`
  have hscale : ∀ x ∈ (⟨m + 1, 0⟩ : TriadicCube 2).vertices,
      ((planarPartCube ω x).scale : ℝ) ≤ c₀ / 192 * ((m : ℝ) + 1) := by
    intro x hx
    have h := (h5 (m + 1) (h5m.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)))).2 x hx
    rw [← Real.rpow_natCast, Real.rpow_le_rpow_left_iff (by norm_num)] at h
    refine h.trans ?_
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have hc : c₀ / 192 * (384 / c₀) = 2 := by
      rw [div_mul_div_comm, mul_comm c₀ 384, mul_div_mul_right _ _ hc₀0.ne']
      norm_num
    have e : c₀ / 192 * ((m : ℝ) + 1) * (2 + 384 / c₀) =
        c₀ / 96 * ((m : ℝ) + 1) + 2 * (m + 1) := by
      calc c₀ / 192 * ((m : ℝ) + 1) * (2 + 384 / c₀) =
            c₀ / 96 * ((m : ℝ) + 1) + c₀ / 192 * (384 / c₀) * (m + 1) := by ring
        _ = c₀ / 96 * ((m : ℝ) + 1) + 2 * (m + 1) := by rw [hc]
    rw [e]
    have : 0 ≤ c₀ / 96 * ((m : ℝ) + 1) := by positivity
    linarith
  set k₀ := ⌊c₀ / 192 * ((m : ℝ) + 1)⌋₊
  have hk₀sc : ∀ x ∈ (⟨m + 1, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k₀ :=
    fun x hx => Nat.le_floor (hscale x hx)
  have hk₀r : (k₀ : ℝ) ≤ c₀ / 192 * ((m : ℝ) + 1) := Nat.floor_le (by positivity)
  have hk₀k : k₀ ≤ k := by
    refine Nat.floor_le_of_le ?_
    have hmk' : (m : ℝ) ≤ 8 * k := by exact_mod_cast hmk
    have h1 : c₀ / 192 ≤ 1 / 384 := by linarith
    have := mul_le_mul h1 (show (m : ℝ) + 1 ≤ 8 * k + 1 by linarith) (by positivity)
      (by norm_num)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    linarith
  have hk₀m : k₀ ≤ m := hk₀k.trans (by omega)
  have hU : PlanarResolved ω ⟨m, 0⟩ := fun z hz =>
    (hk₀sc z (origin_vertices_subset_succ' m hz)).trans hk₀m
  have hbig : 2 * (3 ^ (4 * k) + 3) + 3 * 3 ^ k ≤ 3 ^ m := by
    have h4k : 4 * k + 2 ≤ m := by omega
    have ha : 3 ^ k ≤ 3 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have ha3 : 3 ≤ 3 ^ (4 * k) :=
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * (3 ^ (4 * k) + 3) + 3 * 3 ^ k ≤ 9 * 3 ^ (4 * k) := by linarith
      _ = 3 ^ (4 * k + 2) := by ring
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) h4k
  -- the convergence of `μ` and `ν`
  have hconvT := hN m hNm'
  have hμ : ∀ T : TriadicCube 2, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices →
      ∀ q : Fin 2 → ℝ, |(∑ j, q j ^ 2 / σ) / 2 + planarMu ω T q| ≤
        Cc * (3 : ℝ) ^ (-(αc * m)) * ∑ j, q j ^ 2 := by
    intro T hT hTs q
    have h := (hconvT T hT hTs q 0).1
    rw [hA, smul_one_inv_mulVec_two hσ.ne'] at h
    rw [show (∑ j, q j ^ 2 / σ) / 2 + planarMu ω T q = planarMu ω T q + (∑ j, q j ^ 2 / σ) / 2
      from add_comm _ _]
    refine h.trans (le_of_eq ?_)
    rw [Fin.sum_univ_two]
    ring
  have hν : ∀ T : TriadicCube 2, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices →
      ∀ ξ : Fin 2 → ℝ, |planarNu ω T ξ - σ * (∑ j, ξ j ^ 2) / 2| ≤
        Cc * (3 : ℝ) ^ (-(αc * m)) * ∑ j, ξ j ^ 2 := by
    intro T hT hTs ξ
    have h := (hconvT T hT hTs 0 ξ).2
    rw [hA, smul_one_mulVec_two] at h
    refine h.trans (le_of_eq ?_)
    rw [Fin.sum_univ_two]
    ring
  have hε : Cc * (3 : ℝ) ^ (-(αc * m)) ≤ E * ((3 : ℝ) ^ k) ^ (-c₀) := by
    have hexp : -(αc * m) ≤ 7 * αc + -(c₀ * k) := by
      have h1 : (8 * k : ℝ) ≤ m + 7 := by exact_mod_cast h8k
      have h2 : c₀ * k ≤ 8 * αc * k := mul_le_mul_of_nonneg_right hc₀α (by positivity)
      nlinarith
    calc Cc * (3 : ℝ) ^ (-(αc * m)) ≤ Cc * (3 : ℝ) ^ (7 * αc + -(c₀ * k)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
            hCc.le
      _ = E * ((3 : ℝ) ^ k) ^ (-c₀) := by
        rw [Real.rpow_add (by norm_num), ← Real.rpow_natCast (3 : ℝ) k,
          ← Real.rpow_mul (by norm_num), show (k : ℝ) * -c₀ = -(c₀ * k) by ring, hEdef, mul_assoc]
  -- the moments and the datum
  have hm1 := ((h1 m h1m).1).trans
    ((le_max_left C1 C2).trans (le_max_left (max C1 C2) (max C3 C4)))
  have hm2 := ((h2 m h2m).1).trans
    ((le_max_right C1 C2).trans (le_max_left (max C1 C2) (max C3 C4)))
  have hm3 := ((h3 m h3m).1).trans
    ((le_max_left C3 C4).trans (le_max_right (max C1 C2) (max C3 C4)))
  have hm4 := ((h4 m h4m).1).trans
    ((le_max_right C3 C4).trans (le_max_right (max C1 C2) (max C3 C4)))
  refine ⟨hP, hU, fun u hu => ?_⟩
  set M := planarGradNorm ω m p' u
  have hM0 : 0 ≤ M := planarGradNorm_nonneg ω m p' u
  have hd2 := sum_abs_grad_planarDatum_rpow_div_le hP hU (s := 2) (p' := p') (CM := CM)
    (by norm_num) hp' hm1 hm2 u
  have hdt := sum_abs_grad_planarDatum_rpow_div_le hP hU (s := t) (p' := p') (CM := CM)
    (by linarith) htp hm3 hm4 u
  simp only [Real.rpow_two, sq_abs] at hd2
  have hS2div : innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) / 9 ^ m ≤
      A2 * M ^ 2 := hd2
  have hS2 : innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) ≤
      ((3 : ℝ) ^ m) ^ 2 * (A2 * M ^ 2) := by
    rw [← nine_pow_eq]
    exact ((div_le_iff₀ (by positivity)).1 hS2div).trans_eq (mul_comm _ _)
  have hSt : innerRpowSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) t /
      ((3 : ℝ) ^ m) ^ 2 ≤ At * M ^ t := by
    rw [← nine_pow_eq]
    exact hdt
  have hc := hchain ω hP m k k₀ hk₀k hbig hk₀sc hU (by positivity) hμ hν hγ0 hγ ht hγt u hu
  have hb := chain_le (k₀ := k₀) hσ ht hγ0 hγt hE0 hA20 hAt0 hM0 hK₀0 hC₃ hCA hc₀h hc₀t hc₀γ h8k
    hε (innerSqSum_nonneg _ _) hS2 (innerRpowSum_nonneg _ _ _) hSt
  have hrate := three_pow_rate_le hc₀0 hmk hk₀r
  set R := (3 : ℝ) ^ (-(c₀ / 32 * (m : ℝ)))
  have hsum : ∑ x ∈ clusterVertices ω ⟨m, 0⟩, (u x - dirichletSolution (constCond fun _ => σ)
      (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u) x) ^ 2 ≤
      B * 3 ^ (c₀ / 16) * (((3 : ℝ) ^ m) ^ 4 * M ^ 2 * R ^ 2) := by
    refine (hc.trans hb).trans ?_
    calc B * (((3 : ℝ) ^ k₀) ^ 12 * (((3 : ℝ) ^ m) ^ 4 * M ^ 2 * ((3 : ℝ) ^ k) ^ (-c₀)))
        = B * (((3 : ℝ) ^ m) ^ 4 * M ^ 2) * (((3 : ℝ) ^ k₀) ^ 12 * ((3 : ℝ) ^ k) ^ (-c₀)) := by
          ring
      _ ≤ B * (((3 : ℝ) ^ m) ^ 4 * M ^ 2) * (3 ^ (c₀ / 16) * R ^ 2) :=
          mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = B * 3 ^ (c₀ / 16) * (((3 : ℝ) ^ m) ^ 4 * M ^ 2 * R ^ 2) := by ring
  refine ⟨dirichletSolution (constCond fun _ => σ)
    (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u),
    fun x hx => condLaplacian_constCond_one_eq_zero hσ _ _ hx, fun x hx hxi => ?_, ?_, ?_⟩
  · rw [dirichletSolution_eq_of_not_mem _ _ _ hxi]
    exact boundaryInterpolation_of_mem _ u (Finset.mem_filter.2 ⟨hx, hxi⟩)
  · calc innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
          (dirichletSolution (constCond fun _ => σ)
            (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) / 9 ^ m
        ≤ innerSqSum (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (planarDatum hP m hU u) / 9 ^ m :=
          div_le_div_of_nonneg_right (innerEdgeEnergy_constCond_one_le hσ _ _) (by positivity)
      _ ≤ A2 * M ^ 2 := hS2div
      _ ≤ Cf * M ^ 2 := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _))
          (sq_nonneg _)
  · set Bs := √(B * 3 ^ (c₀ / 16))
    have hBs : Bs ^ 2 = B * 3 ^ (c₀ / 16) := Real.sq_sqrt (by positivity)
    have hBs0 : 0 ≤ Bs := Real.sqrt_nonneg _
    have hR0 : 0 ≤ R := by positivity
    have hdiv : (∑ x ∈ clusterVertices ω ⟨m, 0⟩, (u x - dirichletSolution (constCond fun _ => σ)
        (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u) x) ^ 2) /
          9 ^ m ≤ (Bs * (3 : ℝ) ^ m * M * R) ^ 2 := by
      rw [div_le_iff₀ (by positivity), nine_pow_eq]
      refine hsum.trans (le_of_eq ?_)
      rw [mul_pow, mul_pow, mul_pow, hBs]
      ring
    have hsq := (Real.sqrt_le_sqrt hdiv).trans_eq (Real.sqrt_sq (by positivity))
    have h3m : (3 : ℝ) ^ (-(m : ℝ)) * (3 : ℝ) ^ m = 1 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]
    calc _ ≤ (3 : ℝ) ^ (-(m : ℝ)) * (Bs * (3 : ℝ) ^ m * M * R) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Bs * R * M := by
          rw [show (3 : ℝ) ^ (-(m : ℝ)) * (Bs * (3 : ℝ) ^ m * M * R) =
            ((3 : ℝ) ^ (-(m : ℝ)) * (3 : ℝ) ^ m) * (Bs * R * M) by ring, h3m, one_mul]
      _ ≤ Cf * R * M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_left _ _)) hR0) hM0

end Rigidity.Dirichlet
