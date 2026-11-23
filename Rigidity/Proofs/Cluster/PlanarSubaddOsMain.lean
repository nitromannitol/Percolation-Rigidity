import Rigidity.Proofs.Cluster.PlanarSubaddOs

/-!
# Proposition 5.2 of Armstrong and Dario in dimension two: the `O_s` bound

`planar_subadd_os`: there are `r, α, C > 0` such that for every triadic cube `V` the random error
`X(V) = planarSubaddErr p V` of Proposition 5.2 (with `|μ(V, q) + (1/2) q · ā⁻¹ q| ≤ X(V) |q|²` and
`|ν(V, ξ) - (1/2) ξ · ā ξ| ≤ X(V) |ξ|²`, `abs_planarMuErr_le`, `abs_planarNuErr_le`) satisfies
`X(V) ≤ O_r(C 3^{-α scale V})`, displays (5.1) and (5.2) of the source.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

/-- A polynomial in the scale is absorbed by `3^{m s/2}`. -/
theorem exists_poly_le_three_rpow {θ₀ s : ℝ} (hθ₀ : 0 < θ₀) (hs : 0 < s) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ,
      1 + (4 * θ₀ * (1 + Real.log ((9 : ℝ) ^ m))) ^ 4 ≤ C * (3 : ℝ) ^ ((m : ℝ) * (s / 2)) := by
  set A : ℝ := 4 * θ₀ * (1 + 4 / s) with hA
  refine ⟨1 + A ^ 4 * 72, le_add_of_nonneg_right (by positivity), fun m => ?_⟩
  set x : ℝ := Real.log 3 * ((m : ℝ) * (s / 2)) with hx
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := by positivity
  have h3 : (3 : ℝ) ^ ((m : ℝ) * (s / 2)) = Real.exp x := by
    rw [Real.rpow_def_of_pos (by norm_num)]
  have hlog : Real.log ((9 : ℝ) ^ m) = 4 * x / s := by
    rw [Real.log_pow, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow, hx]
    field_simp
    push_cast
    ring
  have hlin : 1 + 4 * x / s ≤ (1 + 4 / s) * (1 + x) := by
    have : 0 ≤ 4 / s := by positivity
    have e : (1 + 4 / s) * (1 + x) = 1 + 4 / s + x + 4 * x / s := by ring
    rw [e]; nlinarith only [this, hx0]
  have hfac := Real.pow_div_factorial_le_exp (1 + x) (by linarith) 4
  have he : Real.exp (1 + x) ≤ 3 * Real.exp x := by
    rw [Real.exp_add]
    have := Real.exp_one_lt_d9
    have h0 := Real.exp_pos x
    nlinarith only [this, h0]
  have h4 : (1 + x) ^ 4 ≤ 72 * Real.exp x := by
    have : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [this, div_le_iff₀ (by norm_num)] at hfac
    linarith
  have hex : 1 ≤ Real.exp x := Real.one_le_exp hx0
  rw [h3, hlog]
  have hb : (4 * θ₀ * (1 + 4 * x / s)) ^ 4 ≤ A ^ 4 * (1 + x) ^ 4 := by
    rw [← mul_pow, hA]
    apply pow_le_pow_left₀ (by positivity)
    have := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 4 * θ₀ by positivity)
    calc 4 * θ₀ * (1 + 4 * x / s) ≤ 4 * θ₀ * ((1 + 4 / s) * (1 + x)) := this
      _ = _ := by ring
  have hA4 : 0 ≤ A ^ 4 := by positivity
  calc 1 + (4 * θ₀ * (1 + 4 * x / s)) ^ 4 ≤ 1 + A ^ 4 * (72 * Real.exp x) :=
        by nlinarith only [hb, h4, hA4]
    _ ≤ _ := by nlinarith only [hex, hA4]

/-- **The `O_{1/4}` bound of the error by the coarse sizes.** -/
theorem osBound_coarse_bound {p : unitInterval} {θ₀ c₃ : ℝ} (hθ₀ : 0 < θ₀) (hc₃ : 0 < c₃)
    (hmom : ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (planarCoarseGood ω) x / θ₀) ^
        (1 : ℝ))) (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp ((TriadicCube.stoppingSize (planarCoarseGood ω) x / θ₀) ^ (1 : ℝ))
        ∂(latticeBondLaw 2 p)) ≤ 2)
    (V : TriadicCube 2) :
    OsBound (latticeBondLaw 2 p) (1 / 4)
      (c₃ * 16 * (1 + (4 * θ₀ * (1 + Real.log ((9 : ℝ) ^ V.scale))) ^ 4))
      (fun ω => c₃ * (1 + coarseMax ω V ^ 4)) := by
  set μ := latticeBondLaw 2 p with hμ
  set T := V.toIntegerCube.vertices with hT
  have hTne : T.Nonempty := ⟨V.toIntegerCube.corner, by
      rw [hT, IntegerCube.mem_vertices]
      intro i
      have : (0 : ℤ) < (V.toIntegerCube.size : ℤ) := by
        change (0 : ℤ) < ((3 ^ V.scale : ℕ) : ℤ); positivity
      constructor <;> omega⟩
  have hS : ∀ a ∈ T, OsBound μ 1 (2 * θ₀)
      (fun ω => TriadicCube.stoppingSize (planarCoarseGood ω) a) :=
    fun a _ => osBound_of_exp_moment hθ₀ (hmom a).1 (hmom a).2
  have hM := osBound_finset_sup' one_pos (by positivity) T hTne
    (fun a ω => TriadicCube.stoppingSize (planarCoarseGood ω) a) hS
  have hcard : (T.card : ℝ) = 9 ^ V.scale := card_toIntegerCube_vertices_eq V
  rw [hcard, div_one, Real.rpow_one] at hM
  set θM : ℝ := 2 * (1 + Real.log ((9 : ℝ) ^ V.scale)) * (2 * θ₀) with hθM
  have hM' : OsBound μ 1 θM (fun ω => coarseMax ω V) := hM
  have hθM0 : 0 ≤ θM := by
    have : 0 ≤ Real.log ((9 : ℝ) ^ V.scale) := Real.log_nonneg (one_le_pow₀ (by norm_num))
    positivity
  have h4 := osBound_pow_of_nonneg hM' (fun ω => coarseMax_nonneg ω V) (n := 4) (by norm_num)
  have h4' : OsBound μ (1 / 4) (θM ^ 4) (fun ω => coarseMax ω V ^ 4) := by simpa using h4
  have h1 := osBound_const μ (1 / 4) 1 zero_le_one
  have hsum := OsBound.add (by norm_num) h1 h4'
  have hmul := OsBound.const_mul hc₃ hsum
  have e2 : (2 : ℝ) ^ (1 / (1 / 4 : ℝ)) = 16 := by
    rw [show (1 : ℝ) / (1 / 4) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [e2] at hmul
  refine OsBound.mono (le_of_eq ?_) (by positivity) (fun ω => le_rfl) hmul
  rw [hθM]
  ring

/-- **Armstrong and Dario, Proposition 5.2, displays (5.1) and (5.2)** (dimension two,
`p > p_c(2)`): there are `r, α, C > 0` such that for every triadic cube `V` the random error
`X(V)` of `μ(V, ·) + (1/2) q · ā⁻¹ q` and `ν(V, ·) - (1/2) ξ · ā ξ` (with `μ = ν = 0` off the
event that the partition exists and resolves `V`) is measurable and `X(V) ≤ O_r(C 3^{-α scale V})`. -/
theorem planar_subadd_os {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ r α C : ℝ, 0 < r ∧ 0 < α ∧ 0 < C ∧ ∀ V : TriadicCube 2,
      Measurable (planarSubaddErr p V) ∧ (∀ ω, 0 ≤ planarSubaddErr p V ω) ∧
      IsOsBond 2 p (planarSubaddErr p V) r (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
      ∀ (ω : Configuration 2) (q ξ : Fin 2 → ℝ),
        |planarMuErr p ω V q| ≤ planarSubaddErr p V ω * (q 0 ^ 2 + q 1 ^ 2) ∧
        |planarNuErr p ω V ξ| ≤ planarSubaddErr p V ω * (ξ 0 ^ 2 + ξ 1 ^ 2) := by
  obtain ⟨K, β, s, c, K', hK, hβ, hs0, hs1, hc, hK', -, hcube⟩ :=
    exists_planarSubaddGood_tail_cube hpc
  obtain ⟨S, hS0, hS⟩ := exists_abs_mulVec_le (planarAhom p)⁻¹
  obtain ⟨Sa, hSa0, hSa⟩ := exists_abs_mulVec_le (planarAhom p)
  obtain ⟨C₀, hC₀, c₀, hc₀, hq₀⟩ := exists_measure_not_mem_planarCoarseGood_le hpc
  obtain ⟨hH, ⟨θ₀, hθ₀, hmom⟩, -⟩ := partition_estimates_general (d := 2) (by norm_num)
    (latticeBondLaw 2 p) planarCoarseGood measurableSet_mem_planarCoarseGood hC₀ hc₀ one_pos hq₀
  obtain ⟨c₃, hc₃⟩ : ∃ c₃ : ℝ, c₃ = 12 * (2108304 + S + 3 + Sa) := ⟨_, rfl⟩
  have hc₃0 : 0 < c₃ := by rw [hc₃]; positivity
  obtain ⟨C'', hC''1, hC''⟩ := exists_poly_le_three_rpow hθ₀ hs0
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = min β (s / 2) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; exact lt_min hβ (by positivity)
  have hαβ : α ≤ β := by rw [hα]; exact min_le_left _ _
  have hαs : α ≤ s / 2 := by rw [hα]; exact min_le_right _ _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 32 * (12 * K + 1024 * c₃ * C'' / c) +
      c₃ * 16 * C'' * (4 * K' / c) + 1 := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    rw [hC]
    have h1 : 0 ≤ 1024 * c₃ * C'' / c := by positivity
    have h2 : 0 ≤ c₃ * 16 * C'' * (4 * K' / c) := by positivity
    nlinarith only [h1, h2, hK]
  have hr : (0 : ℝ) < 1 / 5 := by norm_num
  refine ⟨1 / 5, α, C * 2 ^ (1 / (1 / 5 : ℝ)) * Real.exp 2 ^ (1 / (1 / 5 : ℝ)), hr, hα0,
    by positivity, fun V => ⟨measurable_planarSubaddErr p V, planarSubaddErr_nonneg p V,
      ?_, fun ω q ξ => ⟨abs_planarMuErr_le p ω V q, abs_planarNuErr_le p ω V ξ⟩⟩⟩
  set μ := latticeBondLaw 2 p with hμ
  set m := V.scale with hm
  set u : ℝ := (3 : ℝ) ^ ((m : ℝ) * (s / 2)) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by norm_num) (by positivity)
  have hu0 : 0 < u := by linarith
  set v : ℝ := (3 : ℝ) ^ (-(m : ℝ) * α) with hv
  have hv0 : 0 < v := by positivity
  have hvu : 1 / u ≤ v := by
    rw [hv, hu, div_le_iff₀ (by positivity), ← Real.rpow_add (by norm_num)]
    apply Real.one_le_rpow (by norm_num)
    have : (m : ℝ) * α ≤ (m : ℝ) * (s / 2) :=
      mul_le_mul_of_nonneg_left hαs (Nat.cast_nonneg m)
    linarith
  have hvβ : (3 : ℝ) ^ (-(m : ℝ) * β) ≤ v := by
    rw [hv]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (m : ℝ) * α ≤ (m : ℝ) * β := mul_le_mul_of_nonneg_left hαβ (Nat.cast_nonneg m)
    linarith
  have hX : ((3 : ℝ) ^ m) ^ s = u ^ 2 := by
    rw [three_rpow_natCast_mul, hu, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  -- the bound of the error by the coarse sizes, and its `O_{1/4}` bound
  set a : ℝ := c₃ * 16 * (1 + (4 * θ₀ * (1 + Real.log ((9 : ℝ) ^ m))) ^ 4) with ha
  have ha0 : 0 ≤ a := by
    have : 0 ≤ Real.log ((9 : ℝ) ^ m) := Real.log_nonneg (one_le_pow₀ (by norm_num))
    rw [ha]; positivity
  have hau : a ≤ c₃ * 16 * C'' * u := by
    have := hC'' m
    rw [← hu] at this
    rw [ha]
    have h16 : (0 : ℝ) ≤ c₃ * 16 := by positivity
    calc c₃ * 16 * (1 + (4 * θ₀ * (1 + Real.log ((9 : ℝ) ^ m))) ^ 4) ≤ c₃ * 16 * (C'' * u) :=
          mul_le_mul_of_nonneg_left this h16
      _ = _ := by ring
  have hY := osBound_coarse_bound (p := p) hθ₀ hc₃0 hmom V
  rw [← ha] at hY
  have hdomY : ∀ᵐ ω ∂μ, planarSubaddErr p V ω ≤ c₃ * (1 + coarseMax ω V ^ 4) := by
    filter_upwards [hH] with ω hω
    rw [hc₃]
    exact planarSubaddErr_le_coarseMax hS0 hS hSa0 hSa hω V
  -- the target bound
  have hfinal : OsBound μ (1 / 5) (C * v) (planarSubaddErr p V) := by
    by_cases hA : 2 * K' ≤ Real.exp (c * u ^ 2 / 2)
    · -- the bad event is rare: the product of its indicator and the coarse bound
      set E := {ω : Configuration 2 | ¬ PlanarSubaddGood p ω V K β} with hE
      set θE : ℝ := 2 / (c * u ^ 2) with hθE
      have hθE0 : 0 < θE := by positivity
      have hEμ : μ E ≤ ENNReal.ofReal (Real.exp (-(1 / θE))) := by
        refine (hcube V).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [← hm, hX, hθE, one_div_div]
        calc 2 * K' * Real.exp (-c * u ^ 2) ≤ Real.exp (c * u ^ 2 / 2) * Real.exp (-c * u ^ 2) :=
              mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
          _ = Real.exp (-(c * u ^ 2 / 2)) := by rw [← Real.exp_add]; ring_nf
      have hEind := osBound_indicator μ hθE0 hEμ
      have hprod := OsBound.mul (by norm_num : (0 : ℝ) < 1 / 4) one_pos ha0
        (fun ω => by positivity) (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
        hY hEind
      have e1 : (1 / 4 : ℝ) * 1 / (1 / 4 + 1) = 1 / 5 := by norm_num
      have e2 : (2 : ℝ) ^ (((1 : ℝ) / 4 + 1) / (1 / 4 * 1)) = 32 := by
        rw [show ((1 : ℝ) / 4 + 1) / (1 / 4 * 1) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      rw [e1, e2] at hprod
      have hconst := osBound_const μ (1 / 5) (12 * (K * (3 : ℝ) ^ (-(m : ℝ) * β)))
        (by positivity)
      have hsum := OsBound.add hr hconst hprod
      have e3 : (2 : ℝ) ^ (1 / (1 / 5 : ℝ)) = 32 := by
        rw [show (1 : ℝ) / (1 / 5) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      rw [e3] at hsum
      refine OsBound.mono_ae ?_ ?_ hsum
      · -- the scales
        have h1 : 12 * (K * (3 : ℝ) ^ (-(m : ℝ) * β)) ≤ 12 * K * v := by
          have := mul_le_mul_of_nonneg_left hvβ hK; linarith
        have h2 : a * θE ≤ 32 * c₃ * C'' / c * v := by
          have hcu : 0 < c * u ^ 2 := by positivity
          calc a * θE ≤ c₃ * 16 * C'' * u * θE := mul_le_mul_of_nonneg_right hau hθE0.le
            _ = 32 * c₃ * C'' / c * (1 / u) := by rw [hθE]; field_simp; ring
            _ ≤ 32 * c₃ * C'' / c * v := mul_le_mul_of_nonneg_left hvu (by positivity)
        have h3 : 0 ≤ c₃ * 16 * C'' * (4 * K' / c) := by positivity
        calc 32 * (12 * (K * (3 : ℝ) ^ (-(m : ℝ) * β)) + 32 * (a * θE))
            ≤ 32 * (12 * K * v + 32 * (32 * c₃ * C'' / c * v)) := by gcongr
          _ = 32 * (12 * K + 1024 * c₃ * C'' / c) * v := by ring
          _ ≤ C * v := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hv0.le
      · filter_upwards [hH] with ω hω
        by_cases hg : PlanarSubaddGood p ω V K β
        · have h1 := planarSubaddErr_le_of_good hg
          have h2 : 0 ≤ c₃ * (1 + coarseMax ω V ^ 4) *
              E.indicator (fun _ => (1 : ℝ)) ω := by
            apply mul_nonneg (by positivity)
            exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
          linarith
        · have hωE : ω ∈ E := hg
          rw [Set.indicator_of_mem hωE, mul_one]
          have h1 := planarSubaddErr_le_coarseMax hS0 hS hSa0 hSa hω V
          rw [← hc₃] at h1
          have : 0 ≤ 12 * (K * (3 : ℝ) ^ (-(m : ℝ) * β)) := by positivity
          linarith
    · -- small cubes: the coarse bound alone
      push Not at hA
      have hK'0 : 0 < K' := by
        by_contra h0
        push Not at h0
        have : 2 * K' ≤ 0 := by linarith
        linarith [Real.exp_pos (c * u ^ 2 / 2)]
      have hu2 : u ^ 2 ≤ 4 * K' / c := by
        have h1 := Real.add_one_le_exp (c * u ^ 2 / 2)
        rw [le_div_iff₀ hc]
        nlinarith only [h1, hA, hK'0]
      have haC : a ≤ C * v := by
        have h1 : a ≤ c₃ * 16 * C'' * (4 * K' / c) * v := by
          calc a ≤ c₃ * 16 * C'' * u := hau
            _ = c₃ * 16 * C'' * u ^ 2 * (1 / u) := by field_simp
            _ ≤ c₃ * 16 * C'' * (4 * K' / c) * v := by
                apply mul_le_mul _ hvu (by positivity) (by positivity)
                exact mul_le_mul_of_nonneg_left hu2 (by positivity)
        have h2 : 0 ≤ 32 * (12 * K + 1024 * c₃ * C'' / c) := by positivity
        calc a ≤ c₃ * 16 * C'' * (4 * K' / c) * v := h1
          _ ≤ C * v := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hv0.le
      exact OsBound.mono_ae haC hdomY (hY.of_exponent_le (by norm_num))
  have hIs := isOsBond_of_osBound hr (by positivity) (measurable_planarSubaddErr p V) hfinal
  refine Rigidity.Proofs.S2.IsOsBond.mono_scale hr (by positivity) (le_of_eq ?_)
    (measurable_planarSubaddErr p V) hIs
  rw [hv]
  ring

end Rigidity.Proofs.Cluster
