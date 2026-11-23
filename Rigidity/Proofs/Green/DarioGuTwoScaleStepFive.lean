import Rigidity.Proofs.Green.DarioGuTwoScaleStepTwo
import Rigidity.Proofs.Green.DarioGuTwoScaleGronwall

/-!
# Step 5 of Proposition 4.3 of Dario–Gu: the two integrations in time

Step 5 of the proof of Proposition 4.3 of Dario–Gu (lines 2448-2490 of the source) combines the
differential inequality of Step 2 with the estimates of Steps 3-4 of the source term, first with
`ψ = 1` (which gives (4.40)), then with the weight. Here the estimate of Steps 3-4 is the
hypothesis `Σ_x ψ² u G ≤ E(ψ u) + (2s)^{-1} Σ_x (ψ u)² + Q s^{α - 3}` at each time `s`, and the
weight satisfies `ψ ψ' + κ + ψ²/(2s) ≤ c/s` (the discrete (4.41), `dgWeightTrunc_edgeKappa_bound`).

* `energy_hasDerivAt_le`: `∂_s Σ_x (ψ u)² ≤ (2c/s) Σ_x u² + 2 Q s^{α - 3}`;
* `le_of_hasDerivAt_le_const_add`: the integration of `E' ≤ c₁ + c₂ s^{α - 3}` from `E(τ) = 0`;
* `energy_first_pass`: (4.40), `Σ_x u(t)² ≤ 2Q/(3 - α) (t/τ) τ^{α - 2}`;
* `energy_second_pass`: the weighted bound `Σ_x (ψ u)(t)² ≤ 2 c B₀ (t/τ) τ^{α - 2} + 2Q/(2 - α) τ^{α - 2}`
  from `Σ_x u(s)² ≤ B₀ (s/τ) τ^{α - 2}`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- **The differential inequality of Step 5** at one time `r`. -/
theorem energy_hasDerivAt_le (ω : Configuration 2) {u G ψ ψ' : ℝ → Vertex 2 → ℝ}
    {a b r B B' c Q : ℝ} {D D' : Vertex 2 → ℝ}
    (hD : Summable fun x => D x ^ 2) (hD' : Summable fun x => D' x ^ 2)
    (hu : ∀ s ∈ Set.Ioo a b, ∀ x, |u s x| ≤ D x)
    (hu' : ∀ s ∈ Set.Ioo a b, ∀ x, |openLaplacian ω (u s) x + G s x| ≤ D' x)
    (hψ : ∀ s ∈ Set.Ioo a b, ∀ x, |ψ s x| ≤ B) (hψ' : ∀ s ∈ Set.Ioo a b, ∀ x, |ψ' s x| ≤ B')
    (hdu : ∀ s ∈ Set.Ioo a b, ∀ x,
      HasDerivAt (fun s => u s x) (openLaplacian ω (u s) x + G s x) s)
    (hdψ : ∀ s ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun s => ψ s x) (ψ' s x) s)
    (hr : r ∈ Set.Ioo a b) (hr0 : 0 < r)
    (hsrc : ∑' x, ψ r x ^ 2 * u r x * G r x ≤ openEnergy ω (fun x => ψ r x * u r x) +
      1 / (2 * r) * ∑' x, (ψ r x * u r x) ^ 2 + Q)
    (hwt : ∀ x, ψ r x * ψ' r x + edgeKappa ω (ψ r) x + ψ r x ^ 2 / (2 * r) ≤ c / r) :
    HasDerivAt (fun s => ∑' x, (ψ s x * u s x) ^ 2)
      (∑' x, 2 * (ψ r x * u r x) *
        (ψ' r x * u r x + ψ r x * (openLaplacian ω (u r) x + G r x))) r ∧
      ∑' x, 2 * (ψ r x * u r x) *
        (ψ' r x * u r x + ψ r x * (openLaplacian ω (u r) x + G r x)) ≤
        2 * c / r * ∑' x, u r x ^ 2 + 2 * Q := by
  refine ⟨hasDerivAt_tsum_sq_mul hD hD' hu hu' hψ hψ' hdu hdψ hr, ?_⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hψ r hr 0)
  have hw : Summable fun x => u r x ^ 2 := by
    refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) hD
    rw [← sq_abs (u r x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hu r hr x) 2
  have hLG : Summable fun x => (openLaplacian ω (u r) x + G r x) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) hD'
    rw [← sq_abs (openLaplacian ω (u r) x + G r x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hu' r hr x) 2
  have hG : Summable fun x => G r x ^ 2 :=
    (summable_sq_sub hLG (summable_sq_openLaplacian ω hw)).congr fun x => by ring
  have h1 := tsum_energy_deriv_le ω hw (hψ r hr) (hψ' r hr) hG
  have hψu : Summable fun x => (ψ r x * u r x) ^ 2 := summable_sq_mul_of_abs_le (hψ r hr) hw
  have hA : Summable fun x => u r x ^ 2 * (ψ r x * ψ' r x + edgeKappa ω (ψ r) x) := by
    refine Summable.of_norm_bounded (hw.mul_left (B * B' + 8 * B ^ 2)) fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm (B * B' + 8 * B ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (hψ r hr x) (hψ' r hr x) (abs_nonneg _) hB
    · rw [abs_of_nonneg (edgeKappa_nonneg ω _ x)]
      exact edgeKappa_le_of_abs_le ω (hψ r hr) x
  have hsum : ∑' x, u r x ^ 2 * (ψ r x * ψ' r x + edgeKappa ω (ψ r) x) +
      1 / (2 * r) * ∑' x, (ψ r x * u r x) ^ 2 ≤ c / r * ∑' x, u r x ^ 2 := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← hA.tsum_add (hψu.mul_left _)]
    refine Summable.tsum_le_tsum (fun x => ?_) (hA.add (hψu.mul_left _)) (hw.mul_left _)
    have h2 := mul_le_mul_of_nonneg_left (hwt x) (sq_nonneg (u r x))
    have e : u r x ^ 2 * (ψ r x * ψ' r x + edgeKappa ω (ψ r) x + ψ r x ^ 2 / (2 * r)) =
        u r x ^ 2 * (ψ r x * ψ' r x + edgeKappa ω (ψ r) x) +
          1 / (2 * r) * (ψ r x * u r x) ^ 2 := by
      field_simp
    have e2 : u r x ^ 2 * (c / r) = c / r * u r x ^ 2 := mul_comm _ _
    linarith
  have e3 : 2 * c / r * ∑' x, u r x ^ 2 = 2 * (c / r * ∑' x, u r x ^ 2) := by ring
  rw [e3]
  linarith

/-- **The integration in time of the second pass**: if `E(τ) = 0`, `E` is continuous on `[τ, t]`
and `E'(s) ≤ c₁ + c₂ s^{α - 3}` on `(τ, t)` with `α < 2` and `c₂ ≥ 0`, then
`E(t) ≤ c₁ (t - τ) + c₂/(2 - α) τ^{α - 2}`. -/
theorem le_of_hasDerivAt_le_const_add {E E' : ℝ → ℝ} {τ t c₁ c₂ α : ℝ} (hτ : 0 < τ)
    (hτt : τ ≤ t) (hc₂ : 0 ≤ c₂) (hα : α < 2) (hE : ContinuousOn E (Set.Icc τ t))
    (hd : ∀ s ∈ Set.Ioo τ t, HasDerivAt E (E' s) s)
    (hle : ∀ s ∈ Set.Ioo τ t, E' s ≤ c₁ + c₂ * s ^ (α - 3)) (h0 : E τ = 0) :
    E t ≤ c₁ * (t - τ) + c₂ / (2 - α) * τ ^ (α - 2) := by
  have h2 : 0 < 2 - α := by linarith
  let g : ℝ → ℝ := fun s => E s - c₁ * s + c₂ / (2 - α) * s ^ (α - 2)
  have hgc : ContinuousOn g (Set.Icc τ t) := by
    refine (hE.sub (continuousOn_const.mul continuousOn_id)).add ?_
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const fun s hs => Or.inl (hτ.trans_le hs.1).ne')
  have hgd : ∀ s ∈ interior (Set.Icc τ t), HasDerivWithinAt g
      (E' s - c₁ * 1 + c₂ / (2 - α) * ((α - 2) * s ^ (α - 2 - 1))) (interior (Set.Icc τ t)) s := by
    intro s hs
    rw [interior_Icc] at hs
    have hs0 : s ≠ 0 := (hτ.trans hs.1).ne'
    exact (((hd s hs).sub ((hasDerivAt_id s).const_mul c₁)).add
      ((Real.hasDerivAt_rpow_const (Or.inl hs0)).const_mul _)).hasDerivWithinAt
  have hgn : ∀ s ∈ interior (Set.Icc τ t),
      E' s - c₁ * 1 + c₂ / (2 - α) * ((α - 2) * s ^ (α - 2 - 1)) ≤ 0 := by
    intro s hs
    rw [interior_Icc] at hs
    have e : c₂ / (2 - α) * ((α - 2) * s ^ (α - 2 - 1)) = -(c₂ * s ^ (α - 3)) := by
      rw [show α - 2 - 1 = α - 3 by ring]
      field_simp
      ring
    rw [e]
    linarith [hle s hs]
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc τ t) hgc hgd hgn
  have hgt : g t ≤ g τ := hanti ⟨le_rfl, hτt⟩ ⟨hτt, le_rfl⟩ hτt
  have ht0 : 0 < t := hτ.trans_le hτt
  have hpos : 0 ≤ c₂ / (2 - α) * t ^ (α - 2) := by positivity
  simp only [g, h0] at hgt
  linarith

/-- **The first pass of Step 5** (`ψ = 1`, (4.40) of Dario–Gu in dimension two). -/
theorem energy_first_pass (ω : Configuration 2) {u G : ℝ → Vertex 2 → ℝ} {τ t Q α : ℝ}
    {D D' : Vertex 2 → ℝ} (hτ : 0 < τ) (hτt : τ ≤ t) (hQ : 0 ≤ Q) (hα : α < 3)
    (hD : Summable fun x => D x ^ 2) (hD' : Summable fun x => D' x ^ 2)
    (hu : ∀ s ∈ Set.Ioo τ t, ∀ x, |u s x| ≤ D x)
    (hu' : ∀ s ∈ Set.Ioo τ t, ∀ x, |openLaplacian ω (u s) x + G s x| ≤ D' x)
    (hdu : ∀ s ∈ Set.Ioo τ t, ∀ x,
      HasDerivAt (fun s => u s x) (openLaplacian ω (u s) x + G s x) s)
    (hcont : ContinuousOn (fun s => ∑' x, u s x ^ 2) (Set.Icc τ t)) (h0 : ∀ x, u τ x = 0)
    (hsrc : ∀ s ∈ Set.Ioo τ t, ∑' x, u s x * G s x ≤ openEnergy ω (u s) +
      1 / (2 * s) * ∑' x, u s x ^ 2 + Q * s ^ (α - 3)) :
    ∑' x, u t x ^ 2 ≤ 2 * Q / (3 - α) * (t / τ) * τ ^ (α - 2) := by
  set ψ : ℝ → Vertex 2 → ℝ := fun _ _ => 1 with hψdef
  have hk : ∀ x, edgeKappa ω (fun _ : Vertex 2 => (1 : ℝ)) x = 0 := fun x => by
    simp [edgeKappa]
  have hE : ∀ s, ∑' x, (ψ s x * u s x) ^ 2 = ∑' x, u s x ^ 2 := fun s => by
    simp only [hψdef, one_mul]
  have hstep : ∀ r ∈ Set.Ioo τ t, ∃ E' : ℝ,
      HasDerivAt (fun s => ∑' x, u s x ^ 2) E' r ∧
        E' ≤ (∑' x, u r x ^ 2) / r + 2 * Q * r ^ (α - 3) := by
    intro r hr
    have hr0 : 0 < r := hτ.trans hr.1
    obtain ⟨h1, h2⟩ := energy_hasDerivAt_le ω (ψ := ψ) (ψ' := fun _ _ => 0) (B := 1) (B' := 0)
      (c := 1 / 2) (Q := Q * r ^ (α - 3)) hD hD' hu hu'
      (fun _ _ _ => by simp [hψdef]) (fun _ _ _ => by simp)
      hdu (fun _ _ _ => hasDerivAt_const _ _) hr hr0
      (by simpa only [hψdef, one_pow, one_mul] using hsrc r hr)
      (fun x => by
        simp only [hψdef, mul_zero, zero_add, one_pow]
        rw [hk x]
        apply le_of_eq
        ring)
    refine ⟨_, ?_, h2.trans (le_of_eq ?_)⟩
    · simpa only [hψdef, one_mul] using h1
    · field_simp
  choose E' hE' using hstep
  classical
  let E'' : ℝ → ℝ := fun s => if hs : s ∈ Set.Ioo τ t then E' s hs else 0
  have h := le_of_hasDerivAt_le_div_add (E := fun s => ∑' x, u s x ^ 2) (E' := E'') hτ hτt
    (by positivity : 0 ≤ 2 * Q) hα hcont
    (fun s hs => by simpa only [E'', dif_pos hs] using (hE' s hs).1)
    (fun s hs => by simpa only [E'', dif_pos hs] using (hE' s hs).2)
    (by simp [h0])
  exact h

/-- **The second pass of Step 5**: the weighted bound from (4.40). -/
theorem energy_second_pass (ω : Configuration 2) {u G ψ ψ' : ℝ → Vertex 2 → ℝ}
    {τ t Q α c B B' B₀ : ℝ} {D D' : Vertex 2 → ℝ} (hτ : 0 < τ) (hτt : τ ≤ t) (hQ : 0 ≤ Q)
    (hα : α < 2) (hc : 0 ≤ c) (hB₀ : 0 ≤ B₀)
    (hD : Summable fun x => D x ^ 2) (hD' : Summable fun x => D' x ^ 2)
    (hu : ∀ s ∈ Set.Ioo τ t, ∀ x, |u s x| ≤ D x)
    (hu' : ∀ s ∈ Set.Ioo τ t, ∀ x, |openLaplacian ω (u s) x + G s x| ≤ D' x)
    (hψ : ∀ s ∈ Set.Ioo τ t, ∀ x, |ψ s x| ≤ B) (hψ' : ∀ s ∈ Set.Ioo τ t, ∀ x, |ψ' s x| ≤ B')
    (hdu : ∀ s ∈ Set.Ioo τ t, ∀ x,
      HasDerivAt (fun s => u s x) (openLaplacian ω (u s) x + G s x) s)
    (hdψ : ∀ s ∈ Set.Ioo τ t, ∀ x, HasDerivAt (fun s => ψ s x) (ψ' s x) s)
    (hcont : ContinuousOn (fun s => ∑' x, (ψ s x * u s x) ^ 2) (Set.Icc τ t))
    (h0 : ∀ x, u τ x = 0)
    (hsrc : ∀ s ∈ Set.Ioo τ t, ∑' x, ψ s x ^ 2 * u s x * G s x ≤
      openEnergy ω (fun x => ψ s x * u s x) + 1 / (2 * s) * ∑' x, (ψ s x * u s x) ^ 2 +
        Q * s ^ (α - 3))
    (hwt : ∀ s ∈ Set.Ioo τ t, ∀ x,
      ψ s x * ψ' s x + edgeKappa ω (ψ s) x + ψ s x ^ 2 / (2 * s) ≤ c / s)
    (hfirst : ∀ s ∈ Set.Ioo τ t, ∑' x, u s x ^ 2 ≤ B₀ * (s / τ) * τ ^ (α - 2)) :
    ∑' x, (ψ t x * u t x) ^ 2 ≤
      2 * c * B₀ * (t / τ) * τ ^ (α - 2) + 2 * Q / (2 - α) * τ ^ (α - 2) := by
  have hstep : ∀ r ∈ Set.Ioo τ t, ∃ E' : ℝ,
      HasDerivAt (fun s => ∑' x, (ψ s x * u s x) ^ 2) E' r ∧
        E' ≤ 2 * c * B₀ * τ ^ (α - 3) + 2 * Q * r ^ (α - 3) := by
    intro r hr
    have hr0 : 0 < r := hτ.trans hr.1
    obtain ⟨h1, h2⟩ := energy_hasDerivAt_le ω (Q := Q * r ^ (α - 3)) hD hD' hu hu' hψ hψ'
      hdu hdψ hr hr0 (hsrc r hr) (hwt r hr)
    refine ⟨_, h1, h2.trans ?_⟩
    have hf := hfirst r hr
    have hτ3 : τ ^ (α - 2) = τ ^ (α - 3) * τ := by
      rw [show α - 2 = α - 3 + 1 by ring, Real.rpow_add_one hτ.ne']
    have e : 2 * c / r * (B₀ * (r / τ) * τ ^ (α - 2)) = 2 * c * B₀ * τ ^ (α - 3) := by
      rw [hτ3]
      field_simp
    have hcr : 0 ≤ 2 * c / r := by positivity
    have := mul_le_mul_of_nonneg_left hf hcr
    linarith
  choose E' hE' using hstep
  classical
  let E'' : ℝ → ℝ := fun s => if hs : s ∈ Set.Ioo τ t then E' s hs else 0
  have h := le_of_hasDerivAt_le_const_add (E := fun s => ∑' x, (ψ s x * u s x) ^ 2) (E' := E'')
    hτ hτt (by positivity : 0 ≤ 2 * Q) hα hcont
    (fun s hs => by simpa only [E'', dif_pos hs] using (hE' s hs).1)
    (fun s hs => by simpa only [E'', dif_pos hs] using (hE' s hs).2)
    (by simp [h0])
  have hτ3 : τ ^ (α - 2) = τ ^ (α - 3) * τ := by
    rw [show α - 2 = α - 3 + 1 by ring, Real.rpow_add_one hτ.ne']
  have hτp : 0 ≤ τ ^ (α - 3) := by positivity
  have e : 2 * c * B₀ * (t / τ) * τ ^ (α - 2) = 2 * c * B₀ * τ ^ (α - 3) * t := by
    rw [hτ3]
    field_simp
  have h4 : 2 * c * B₀ * τ ^ (α - 3) * (t - τ) ≤ 2 * c * B₀ * τ ^ (α - 3) * t := by
    have : 0 ≤ 2 * c * B₀ * τ ^ (α - 3) := by positivity
    nlinarith
  linarith

end Rigidity.Green
