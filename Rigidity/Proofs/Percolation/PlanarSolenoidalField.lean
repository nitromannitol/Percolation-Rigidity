import Rigidity.Proofs.Percolation.PlanarCubeEnergy

/-!
# A bounded solenoidal lattice vector field equal to a constant on a triadic cube

Step 1 of the proof of Lemma 5.6 of Armstrong and Dario constructs, for a unit direction `e`, a
bounded vector field on the lattice edges which equals `e` on the cube `□_n`, vanishes far away,
and is almost divergence free, by discretizing a smooth divergence-free continuum field. In
dimension two we take instead the discrete curl of a stream function on the plaquettes: for
`ψ : ℤ² → ℝ` (the value at the plaquette with lower left corner `z`), the flow through the edge
`(x, x + e₀)` is `ψ(x) - ψ(x - e₁)` and through `(x, x + e₁)` is `ψ(x - e₀) - ψ(x)`. Such a flow is
exactly divergence free. With the stream function `ψ(z) = (e₀ z₁ - e₁ z₀) χ_n(z)`, where `χ_n` is a
cutoff equal to `1` on `{|z|_∞ ≤ 3ⁿ}` and to `0` on `{|z|_∞ ≥ (5/4) 3ⁿ}` with slope `4 · 3⁻ⁿ`, the flow
equals `e` on the edges near `□_n`, is bounded by `10 |e|₁` and vanishes outside
`{|x|_∞ < (5/4) 3ⁿ + 1}`.
-/

open LatticeProb.Percolation

namespace Rigidity.Percolation

/-- The discrete curl of a stream function on the plaquettes: the flow through the lattice edge
`(x, x + e_i)`. -/
noncomputable def curlFlow (ψ : Vertex 2 → ℝ) (x : Vertex 2) (i : Fin 2) : ℝ :=
  if i = 0 then ψ x - ψ (x - unitVertex 1) else ψ (x - unitVertex 0) - ψ x

/-- **Curls are divergence free.** -/
theorem sum_curlFlow_sub_eq_zero (ψ : Vertex 2 → ℝ) (x : Vertex 2) :
    ∑ i : Fin 2, (curlFlow ψ x i - curlFlow ψ (x - unitVertex i) i) = 0 := by
  rw [Fin.sum_univ_two]
  unfold curlFlow
  simp only [if_neg (show (1 : Fin 2) ≠ 0 by decide), ↓reduceIte]
  rw [sub_right_comm x (unitVertex 0) (unitVertex 1)]
  ring

theorem sub_unitVertex_apply_self (x : Vertex 2) (i : Fin 2) :
    (x - unitVertex i) i = x i - 1 := by
  simp [unitVertex]

theorem sub_unitVertex_apply_ne (x : Vertex 2) {i j : Fin 2} (h : j ≠ i) :
    (x - unitVertex i) j = x j := by
  simp [unitVertex, h]

/-- The curl of an affine stream function `a z₁ - b z₀` is the constant flow `(a, b)`. -/
theorem curlFlow_of_affine {ψ : Vertex 2 → ℝ} {a b : ℝ} {x : Vertex 2}
    (h : ∀ z, z = x ∨ z = x - unitVertex 0 ∨ z = x - unitVertex 1 →
      ψ z = a * (z 1 : ℝ) - b * (z 0 : ℝ)) (i : Fin 2) :
    curlFlow ψ x i = ![a, b] i := by
  have h0 := h x (Or.inl rfl)
  have h1 := h (x - unitVertex 0) (Or.inr (Or.inl rfl))
  have h2 := h (x - unitVertex 1) (Or.inr (Or.inr rfl))
  rw [sub_unitVertex_apply_self, sub_unitVertex_apply_ne x (by decide : (1 : Fin 2) ≠ 0)] at h1
  rw [sub_unitVertex_apply_self, sub_unitVertex_apply_ne x (by decide : (0 : Fin 2) ≠ 1)] at h2
  fin_cases i
  · simp only [curlFlow, Fin.zero_eta, Matrix.cons_val_zero]
    rw [h0, h2]
    push_cast
    ring
  · simp only [curlFlow, Fin.mk_one, if_neg (by decide : (1 : Fin 2) ≠ 0), Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [h0, h1]
    push_cast
    ring

/-- The sup norm of a planar vertex, as a real number. -/
noncomputable def supNorm (z : Vertex 2) : ℝ := max |(z 0 : ℝ)| |(z 1 : ℝ)|

theorem supNorm_nonneg (z : Vertex 2) : 0 ≤ supNorm z := le_max_of_le_left (abs_nonneg _)

theorem supNorm_sub_unitVertex_le (z : Vertex 2) (i : Fin 2) :
    supNorm (z - unitVertex i) ≤ supNorm z + 1 ∧ supNorm z ≤ supNorm (z - unitVertex i) + 1 := by
  have key : ∀ j : Fin 2, |((z - unitVertex i) j : ℝ)| ≤ |(z j : ℝ)| + 1 ∧
      |(z j : ℝ)| ≤ |((z - unitVertex i) j : ℝ)| + 1 := by
    intro j
    by_cases hij : j = i
    · subst hij
      rw [sub_unitVertex_apply_self]
      push_cast
      constructor
      · calc |(z j : ℝ) - 1| ≤ |(z j : ℝ)| + |(1 : ℝ)| := abs_sub _ _
          _ = |(z j : ℝ)| + 1 := by rw [abs_one]
      · calc |(z j : ℝ)| = |((z j : ℝ) - 1) + 1| := by ring_nf
          _ ≤ |(z j : ℝ) - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ = |(z j : ℝ) - 1| + 1 := by rw [abs_one]
    · rw [sub_unitVertex_apply_ne z hij]
      exact ⟨by linarith, by linarith⟩
  unfold supNorm
  constructor
  · exact max_le ((key 0).1.trans (by linarith [le_max_left |(z 0 : ℝ)| |(z 1 : ℝ)|]))
      ((key 1).1.trans (by linarith [le_max_right |(z 0 : ℝ)| |(z 1 : ℝ)|]))
  · refine max_le ((key 0).2.trans ?_) ((key 1).2.trans ?_)
    · linarith [le_max_left |((z - unitVertex i) 0 : ℝ)| |((z - unitVertex i) 1 : ℝ)|]
    · linarith [le_max_right |((z - unitVertex i) 0 : ℝ)| |((z - unitVertex i) 1 : ℝ)|]

/-- The cutoff `χ_n`, equal to `1` on `{|z|_∞ ≤ 3ⁿ}` and to `0` on `{|z|_∞ ≥ (5/4) 3ⁿ}`. -/
noncomputable def planarCutoff (n : ℕ) (z : Vertex 2) : ℝ :=
  max 0 (min 1 (5 - 4 * supNorm z / 3 ^ n))

theorem planarCutoff_nonneg (n : ℕ) (z : Vertex 2) : 0 ≤ planarCutoff n z := le_max_left _ _

theorem planarCutoff_le_one (n : ℕ) (z : Vertex 2) : planarCutoff n z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem planarCutoff_eq_one {n : ℕ} {z : Vertex 2} (hz : supNorm z ≤ 3 ^ n) :
    planarCutoff n z = 1 := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have : 1 ≤ 5 - 4 * supNorm z / 3 ^ n := by
    rw [le_sub_comm, div_le_iff₀ h3]
    linarith
  rw [planarCutoff, min_eq_left this, max_eq_right zero_le_one]

theorem planarCutoff_eq_zero {n : ℕ} {z : Vertex 2} (hz : 5 / 4 * 3 ^ n ≤ supNorm z) :
    planarCutoff n z = 0 := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have : 5 - 4 * supNorm z / 3 ^ n ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ h3]
    linarith
  rw [planarCutoff, max_eq_left ((min_le_right _ _).trans this)]

theorem abs_planarCutoff_sub_le (n : ℕ) (z z' : Vertex 2) :
    |planarCutoff n z - planarCutoff n z'| ≤ 4 * |supNorm z - supNorm z'| / 3 ^ n := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 (5 - 4 * supNorm z / 3 ^ n)) 0
    (min 1 (5 - 4 * supNorm z' / 3 ^ n))
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (5 - 4 * supNorm z / 3 ^ n) 1
    (5 - 4 * supNorm z' / 3 ^ n)
  simp only [sub_self, abs_zero] at h1 h2
  have e : |5 - 4 * supNorm z / 3 ^ n - (5 - 4 * supNorm z' / 3 ^ n)| =
      4 * |supNorm z - supNorm z'| / 3 ^ n := by
    rw [show 5 - 4 * supNorm z / 3 ^ n - (5 - 4 * supNorm z' / 3 ^ n) =
      -(4 / 3 ^ n) * (supNorm z - supNorm z') by field_simp; ring, abs_mul, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 4 / 3 ^ n)]
    ring
  rw [e] at h2
  unfold planarCutoff
  have h0 : 0 ≤ 4 * |supNorm z - supNorm z'| / 3 ^ n := by positivity
  calc _ ≤ max 0 |min 1 (5 - 4 * supNorm z / 3 ^ n) - min 1 (5 - 4 * supNorm z' / 3 ^ n)| := h1
    _ ≤ _ := max_le h0 (h2.trans (max_le h0 le_rfl))

/-- **The solenoidal field** in direction `e` at scale `n`: the curl of the stream function
`(e₀ z₁ - e₁ z₀) χ_n(z)`. -/
noncomputable def solenoidalField (n : ℕ) (e : Fin 2 → ℝ) : Vertex 2 → Fin 2 → ℝ :=
  curlFlow fun z => (e 0 * (z 1 : ℝ) - e 1 * (z 0 : ℝ)) * planarCutoff n z

/-- **The solenoidal field is divergence free.** -/
theorem sum_solenoidalField_sub_eq_zero (n : ℕ) (e : Fin 2 → ℝ) (x : Vertex 2) :
    ∑ i : Fin 2, (solenoidalField n e x i - solenoidalField n e (x - unitVertex i) i) = 0 :=
  sum_curlFlow_sub_eq_zero _ x

/-- **The solenoidal field equals `e` near `□_n`.** -/
theorem solenoidalField_eq {n : ℕ} (e : Fin 2 → ℝ) {x : Vertex 2} (hx : supNorm x + 1 ≤ 3 ^ n)
    (i : Fin 2) : solenoidalField n e x i = e i := by
  have h : ∀ z, z = x ∨ z = x - unitVertex 0 ∨ z = x - unitVertex 1 →
      (e 0 * (z 1 : ℝ) - e 1 * (z 0 : ℝ)) * planarCutoff n z =
        e 0 * (z 1 : ℝ) - e 1 * (z 0 : ℝ) := by
    rintro z (rfl | rfl | rfl)
    · rw [planarCutoff_eq_one (by linarith [supNorm_nonneg z]), mul_one]
    · rw [planarCutoff_eq_one (by linarith [(supNorm_sub_unitVertex_le x 0).1]), mul_one]
    · rw [planarCutoff_eq_one (by linarith [(supNorm_sub_unitVertex_le x 1).1]), mul_one]
  rw [solenoidalField, curlFlow_of_affine h i]
  fin_cases i <;> rfl

/-- **The solenoidal field vanishes far from `□_n`.** -/
theorem solenoidalField_eq_zero {n : ℕ} (e : Fin 2 → ℝ) {x : Vertex 2}
    (hx : 5 / 4 * 3 ^ n + 1 ≤ supNorm x) (i : Fin 2) : solenoidalField n e x i = 0 := by
  have hz : ∀ j : Fin 2, planarCutoff n (x - unitVertex j) = 0 := fun j =>
    planarCutoff_eq_zero (by linarith [(supNorm_sub_unitVertex_le x j).2])
  have hx0 : planarCutoff n x = 0 := planarCutoff_eq_zero (by linarith)
  simp only [solenoidalField, curlFlow]
  split_ifs <;> simp [hz, hx0]

/-- One term of the bound: the increment of the stream function across an edge. -/
theorem abs_stream_sub_le (n : ℕ) (e : Fin 2 → ℝ) (z : Vertex 2) (j : Fin 2) :
    |(e 0 * (z 1 : ℝ) - e 1 * (z 0 : ℝ)) * planarCutoff n z -
        (e 0 * ((z - unitVertex j) 1 : ℝ) - e 1 * ((z - unitVertex j) 0 : ℝ)) *
          planarCutoff n (z - unitVertex j)| ≤ 10 * (|e 0| + |e 1|) := by
  set z' := z - unitVertex j
  set f : Vertex 2 → ℝ := fun w => e 0 * (w 1 : ℝ) - e 1 * (w 0 : ℝ) with hf
  have hE : 0 ≤ |e 0| + |e 1| := by positivity
  have hfz : ∀ w, |f w| ≤ (|e 0| + |e 1|) * supNorm w := fun w => by
    simp only [hf]
    calc |e 0 * (w 1 : ℝ) - e 1 * (w 0 : ℝ)| ≤ |e 0 * (w 1 : ℝ)| + |e 1 * (w 0 : ℝ)| :=
          abs_sub _ _
      _ = |e 0| * |(w 1 : ℝ)| + |e 1| * |(w 0 : ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ |e 0| * supNorm w + |e 1| * supNorm w := by
          gcongr
          · exact le_max_right _ _
          · exact le_max_left _ _
      _ = _ := by ring
  have hdiff : |f z - f z'| ≤ |e 0| + |e 1| := by
    simp only [hf, z']
    fin_cases j
    · rw [Fin.zero_eta, sub_unitVertex_apply_self,
        sub_unitVertex_apply_ne z (by decide : (1 : Fin 2) ≠ 0)]
      push_cast
      rw [show e 0 * (z 1 : ℝ) - e 1 * (z 0 : ℝ) - (e 0 * (z 1 : ℝ) - e 1 * ((z 0 : ℝ) - 1)) =
        -e 1 by ring, abs_neg]
      linarith [abs_nonneg (e 0)]
    · rw [Fin.mk_one, sub_unitVertex_apply_self,
        sub_unitVertex_apply_ne z (by decide : (0 : Fin 2) ≠ 1)]
      push_cast
      rw [show e 0 * (z 1 : ℝ) - e 1 * (z 0 : ℝ) - (e 0 * ((z 1 : ℝ) - 1) - e 1 * (z 0 : ℝ)) =
        e 0 by ring]
      linarith [abs_nonneg (e 1)]
  have hχ := abs_planarCutoff_sub_le n z z'
  have hs := supNorm_sub_unitVertex_le z j
  have hsd : |supNorm z - supNorm z'| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have h31 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hχ' : |planarCutoff n z - planarCutoff n z'| ≤ 4 / 3 ^ n :=
    hχ.trans (div_le_div_of_nonneg_right (by linarith) h3.le)
  have hz1 := planarCutoff_le_one n z
  have hz0 := planarCutoff_nonneg n z
  -- the second term vanishes unless `z'` is in the support region
  have hsecond : |f z'| * |planarCutoff n z - planarCutoff n z'| ≤ 9 * (|e 0| + |e 1|) := by
    by_cases hfar : 5 / 4 * 3 ^ n + 1 ≤ supNorm z'
    · rw [planarCutoff_eq_zero (by linarith : 5 / 4 * 3 ^ n ≤ supNorm z),
        planarCutoff_eq_zero (by linarith : 5 / 4 * 3 ^ n ≤ supNorm z'), sub_self, abs_zero,
        mul_zero]
      positivity
    · replace hfar := not_le.1 hfar
      have hf' : |f z'| ≤ (|e 0| + |e 1|) * (5 / 4 * 3 ^ n + 1) :=
        (hfz z').trans (mul_le_mul_of_nonneg_left hfar.le hE)
      calc |f z'| * |planarCutoff n z - planarCutoff n z'|
          ≤ (|e 0| + |e 1|) * (5 / 4 * 3 ^ n + 1) * (4 / 3 ^ n) :=
            mul_le_mul hf' hχ' (abs_nonneg _) (by positivity)
        _ = (|e 0| + |e 1|) * (5 + 4 / 3 ^ n) := by field_simp
        _ ≤ (|e 0| + |e 1|) * 9 := by
            gcongr
            have : 4 / (3 : ℝ) ^ n ≤ 4 := div_le_self (by norm_num) h31
            linarith
        _ = 9 * (|e 0| + |e 1|) := by ring
  have e1 : f z * planarCutoff n z - f z' * planarCutoff n z' =
      (f z - f z') * planarCutoff n z + f z' * (planarCutoff n z - planarCutoff n z') := by ring
  change |f z * planarCutoff n z - f z' * planarCutoff n z'| ≤ _
  rw [e1]
  calc _ ≤ |(f z - f z') * planarCutoff n z| + |f z' * (planarCutoff n z - planarCutoff n z')| :=
        abs_add_le _ _
    _ = |f z - f z'| * planarCutoff n z + |f z'| * |planarCutoff n z - planarCutoff n z'| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hz0]
    _ ≤ (|e 0| + |e 1|) * 1 + 9 * (|e 0| + |e 1|) := by
        gcongr
    _ = _ := by ring

/-- **The solenoidal field is bounded** by `10 |e|₁`. -/
theorem abs_solenoidalField_le (n : ℕ) (e : Fin 2 → ℝ) (x : Vertex 2) (i : Fin 2) :
    |solenoidalField n e x i| ≤ 10 * (|e 0| + |e 1|) := by
  simp only [solenoidalField, curlFlow]
  split_ifs
  · exact abs_stream_sub_le n e x 1
  · rw [abs_sub_comm]
    exact abs_stream_sub_le n e x 0

end Rigidity.Percolation
