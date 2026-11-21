import Rigidity.Proofs.Cluster.Meyers

/-!
# The Meyers estimate on triadic cubes

`meyers_triadic` is the deterministic content of Armstrong–Dario, *Elliptic regularity and
quantitative homogenization on percolation clusters*, Proposition 3.8, stated for a function `G ≥ 0`
(in the application `G = |∇u 1_{𝐚≠0}|²` on `𝒞_*(□_{m+1})`, extended by zero, so that
`G^{1+ε/2} = |∇u 1_{𝐚≠0}|^{2+ε}`) and a partition of `ℤ^d` into triadic cells `cube (s x) x`;
see the module `Rigidity.Proofs.Cluster.Meyers` for the hypotheses. Step 2 applies
`gehring_triadic` to `g = (avg_{cell} G^θ)^{1/θ}`, `θ = d/(d+1)`, with the enlargement `9□`, and
Step 3 removes the cell sizes by Hölder's inequality with the exponents `p = (1+ε)/(1+ε/2)` and
`q = 2(1+ε)/ε`, using `G(x)^θ ≤ |cell(x)| avg_{cell(x)} G^θ` and the moment bound
`∑_{x ∈ □} size(cell(x))^t ≤ K |□|`, `t = d q (1+ε/2)/θ` (the exponent
`t = (2+ε)(1+ε)(d+1)/(2ε)` of Armstrong and Dario, with `ε` in place of `ε/2`).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

/-- **The Meyers estimate** (Armstrong–Dario, Proposition 3.8, deterministic part). For `d ≥ 1`,
`A₀ ≥ 1` and `K ≥ 0` there are `ε > 0`, `t > 0` and `C < ∞` such that for every triadic cube
`□ = cube n x₀`, every `G ≥ 0` and every partition into triadic cells `cube (s x) x` whose
neighbouring cells have comparable scales, such that `3□` is a union of cells, the reverse Hölder
inequality `avg_{□'} G ≤ A₀ (avg_{3□'} G^{d/(d+1)})^{(d+1)/d}` holds on every triadic cube `□'`
containing a cell with `3□' ⊆ 3□`, and `∑_{x ∈ □} size(cell(x))^t ≤ K |□|`,
`avg_□ G^{1+ε/2} ≤ C (avg_{3□} G)^{1+ε/2}`. -/
theorem meyers_triadic (hd : 1 ≤ d) {A₀ K : ℝ} (hA₀ : 1 ≤ A₀) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (x₀ : Vertex d) (G : Vertex d → ℝ) (s : Vertex d → ℕ), (∀ x, 0 ≤ G x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          avg (cube k y) G ≤
            A₀ * avg (enl 1 k y) (fun x => G x ^ ((d : ℝ) / (d + 1))) ^ (((d : ℝ) + 1) / d)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => G x ^ (1 + ε / 2)) ≤ C * avg (enl 1 n x₀) G ^ (1 + ε / 2) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set θ : ℝ := (d : ℝ) / (d + 1) with hθdef
  have hθ0 : 0 < θ := div_pos hd' (by linarith)
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one (by linarith)]
    linarith
  have hinv : 1 / θ = ((d : ℝ) + 1) / d := by rw [hθdef, one_div_div]
  have h1θ : 0 < 1 / θ := one_div_pos.mpr hθ0
  set A : ℝ := A₀ * ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) with hAdef
  have hA : 1 ≤ A := by
    have h1 : 1 ≤ ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) :=
      Real.one_le_rpow (one_le_pow₀ (by norm_num)) h1θ.le
    nlinarith
  obtain ⟨ε, hε0, -, CG, hCG0, hGeh⟩ := gehring_triadic (d := d) hθ0 hθ1 hA (j := 2) (by norm_num)
  have hεne : ε ≠ 0 := hε0.ne'
  have h1εne : 1 + ε ≠ 0 := by positivity
  have h2εne : 1 + ε / 2 ≠ 0 := by positivity
  set p : ℝ := (1 + ε) / (1 + ε / 2) with hp
  set q : ℝ := 2 * (1 + ε) / ε with hq
  have hp1 : 1 < p := by
    rw [hp, one_lt_div (by linarith)]
    linarith
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp1, ?_⟩
    rw [hp, hq, inv_div, inv_div]
    field_simp
    ring
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set α : ℝ := 1 / θ * (1 + ε / 2) with hα
  have hα0 : 0 < α := mul_pos h1θ (by linarith)
  set t : ℝ := d * α * q with ht
  have ht0 : 0 < t := mul_pos (mul_pos hd' hα0) hq0
  have hC0 : 0 ≤ CG ^ (1 / p) * K ^ (1 / q) :=
    mul_nonneg (Real.rpow_nonneg hCG0 _) (Real.rpow_nonneg hK _)
  refine ⟨ε, hε0, t, ht0, CG ^ (1 / p) * K ^ (1 / q), hC0, ?_⟩
  intro n x₀ G s hG hcell hnb hΩcell hRH hmom
  set f := cellAvg s G θ with hf
  set g : Vertex d → ℝ := fun x => f x ^ (1 / θ) with hg
  have hf0 : ∀ x, 0 ≤ f x := cellAvg_nonneg s hG θ
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (hf0 x) _
  -- Step 1: the reverse Hölder inequality for `g` with enlargement `9□'`
  have hRH' : ∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
      avg (cube k y) G ≤ A₀ * avg (enl 1 k y) (fun x => G x ^ θ) ^ (1 / θ) := by
    intro k y hk hsub
    rw [hinv]
    exact hRH k y hk hsub
  have hRHg : ∀ k y, enl 2 k y ⊆ enl 1 n x₀ →
      avg (cube k y) g ≤ A * avg (enl 2 k y) (fun x => g x ^ θ) ^ (1 / θ) :=
    fun k y hsub => reverse_holder_cellAvg hcell hnb hG hθ0 hθ1.le hA₀ hRH' k y hsub
  -- Step 2: Gehring's lemma for `g`
  have hgeh := hGeh n x₀ g hg0 hRHg
  set a := avg (enl 1 n x₀) G with ha
  have hΩpos : (0 : ℝ) < (enl 1 n x₀).card := by
    rw [card_enl]
    positivity
  have ha0 : 0 ≤ a := div_nonneg (Finset.sum_nonneg fun x _ => hG x) hΩpos.le
  have hgΩ : avg (enl 1 n x₀) g ≤ a :=
    div_le_div_of_nonneg_right (sum_cellAvg_rpow_le hcell hG hθ0 hθ1.le hΩcell)
      (Nat.cast_nonneg _)
  have hgΩ0 : 0 ≤ avg (enl 1 n x₀) g :=
    div_nonneg (Finset.sum_nonneg fun x _ => hg0 x) hΩpos.le
  have hQpos : (0 : ℝ) < (cube n x₀).card := card_cube_pos n x₀
  have h1ε : 0 ≤ 1 + ε := by linarith
  have hsumg : ∑ x ∈ cube n x₀, g x ^ (1 + ε) ≤ (cube n x₀).card * (CG * a ^ (1 + ε)) := by
    have h1 : avg (cube n x₀) (fun x => g x ^ (1 + ε)) ≤ CG * a ^ (1 + ε) :=
      hgeh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hgΩ0 hgΩ h1ε) hCG0)
    rw [avg, div_le_iff₀ hQpos] at h1
    linarith
  -- Step 3: Hölder's inequality removes the cell sizes
  set w : Vertex d → ℝ := fun x => ((cube (s x) x).card : ℝ) ^ α with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpt : ∀ x, G x ^ (1 + ε / 2) ≤ g x ^ (1 + ε / 2) * w x := by
    intro x
    have hcpos := card_cube_pos (s x) x
    have h1 : G x ^ θ ≤ (cube (s x) x).card * f x := by
      have h2 : G x ^ θ ≤ ∑ z ∈ cube (s x) x, G z ^ θ :=
        Finset.single_le_sum (fun z _ => Real.rpow_nonneg (hG z) θ) (mem_cube_self _ x)
      simp only [hf, cellAvg, avg]
      rw [mul_div_cancel₀ _ hcpos.ne']
      exact h2
    have h3 : G x ≤ ((cube (s x) x).card : ℝ) ^ (1 / θ) * g x := by
      have h4 := Real.rpow_le_rpow (Real.rpow_nonneg (hG x) θ) h1 h1θ.le
      rwa [← Real.rpow_mul (hG x), mul_one_div_cancel hθ0.ne', Real.rpow_one,
        Real.mul_rpow (Nat.cast_nonneg _) (hf0 x)] at h4
    have h5 := Real.rpow_le_rpow (hG x) h3 (by linarith : (0 : ℝ) ≤ 1 + ε / 2)
    rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hg0 x),
      ← Real.rpow_mul (Nat.cast_nonneg _)] at h5
    simp only [hw, hα]
    linarith
  have hHold := Real.inner_le_Lp_mul_Lq_of_nonneg (cube n x₀) hpq
    (f := fun x => g x ^ (1 + ε / 2)) (g := w) (fun x _ => Real.rpow_nonneg (hg0 x) _)
    (fun x _ => hw0 x)
  have hpow1 : ∀ x, (g x ^ (1 + ε / 2)) ^ p = g x ^ (1 + ε) := by
    intro x
    rw [← Real.rpow_mul (hg0 x)]
    congr 1
    rw [hp]
    field_simp
  have hpow2 : ∀ x, w x ^ q = ((3 : ℝ) ^ s x) ^ t := by
    intro x
    simp only [hw]
    rw [← Real.rpow_mul (Nat.cast_nonneg _), card_cube, ← Real.rpow_natCast ((3 : ℝ) ^ s x) d,
      ← Real.rpow_mul (by positivity), ht]
    congr 1
    ring
  simp only [hpow1, hpow2] at hHold
  have hsumG : ∑ x ∈ cube n x₀, G x ^ (1 + ε / 2) ≤
      ((cube n x₀).card * (CG * a ^ (1 + ε))) ^ (1 / p) * (K * (cube n x₀).card) ^ (1 / q) := by
    calc ∑ x ∈ cube n x₀, G x ^ (1 + ε / 2)
        ≤ ∑ x ∈ cube n x₀, g x ^ (1 + ε / 2) * w x := Finset.sum_le_sum fun x _ => hpt x
      _ ≤ (∑ x ∈ cube n x₀, g x ^ (1 + ε)) ^ (1 / p) *
            (∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t) ^ (1 / q) := hHold
      _ ≤ ((cube n x₀).card * (CG * a ^ (1 + ε))) ^ (1 / p) *
            (K * (cube n x₀).card) ^ (1 / q) := by
          refine mul_le_mul (Real.rpow_le_rpow (Finset.sum_nonneg fun x _ =>
            Real.rpow_nonneg (hg0 x) _) hsumg (one_div_pos.mpr hp0).le)
            (Real.rpow_le_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (by positivity) _)
              hmom (one_div_pos.mpr hq0).le) (Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
                Real.rpow_nonneg (by positivity) _) _)
            (Real.rpow_nonneg (mul_nonneg hQpos.le (mul_nonneg hCG0 (Real.rpow_nonneg ha0 _))) _)
  -- the powers of `|□|` and of `a`
  have hexp : (1 + ε) * (1 / p) = 1 + ε / 2 := by
    rw [hp]
    field_simp
  have hpq' : 1 / p + 1 / q = 1 := by
    rw [one_div, one_div]
    exact hpq.inv_add_inv_eq_one
  have hfinal : ((cube n x₀).card * (CG * a ^ (1 + ε))) ^ (1 / p) * (K * (cube n x₀).card) ^ (1 / q)
      = (cube n x₀).card * (CG ^ (1 / p) * K ^ (1 / q) * a ^ (1 + ε / 2)) := by
    rw [Real.mul_rpow hQpos.le (mul_nonneg hCG0 (Real.rpow_nonneg ha0 _)),
      Real.mul_rpow hCG0 (Real.rpow_nonneg ha0 _), Real.mul_rpow hK hQpos.le,
      ← Real.rpow_mul ha0, hexp]
    have hQ : ((cube n x₀).card : ℝ) ^ (1 / p) * ((cube n x₀).card : ℝ) ^ (1 / q) =
        (cube n x₀).card := by
      rw [← Real.rpow_add hQpos, hpq', Real.rpow_one]
    calc ((cube n x₀).card : ℝ) ^ (1 / p) * (CG ^ (1 / p) * a ^ (1 + ε / 2)) *
          (K ^ (1 / q) * ((cube n x₀).card : ℝ) ^ (1 / q))
        = (((cube n x₀).card : ℝ) ^ (1 / p) * ((cube n x₀).card : ℝ) ^ (1 / q)) *
            (CG ^ (1 / p) * K ^ (1 / q) * a ^ (1 + ε / 2)) := by ring
      _ = (cube n x₀).card * (CG ^ (1 / p) * K ^ (1 / q) * a ^ (1 + ε / 2)) := by rw [hQ]
  rw [hfinal] at hsumG
  rw [avg, div_le_iff₀ hQpos]
  linarith

end Rigidity.Proofs.Cluster
