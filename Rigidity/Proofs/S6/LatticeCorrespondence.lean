import Rigidity.Steps.S6.UpperBound
import Mathlib.Analysis.Normed.Ring.Finite

/-! # Section 6: characters of the sandpile group as phase vectors

step:6.5-upper, characters (paper `paper/percolation-harmonic-corrected.tex` L2948-2951; D. C.
Jerison, L. Levine and J. Pike, arXiv 1511.00666, Section 3, multiplicative harmonic functions).
A character `χ` of the finite sandpile group `ℤ^V / Δ_V ℤ^V` has `|χ| = 1`, so
`χ([1_x]) = e^{2πiθ(x)}` with `θ(x) = arg χ([1_x]) / 2π`. Since `[f] = Σ_x f(x) [1_x]`, one has
`χ([f]) = e^{2πi Σ_x f(x) θ(x)}`. The character kills `[Δ_V 1_x]`, and
`Σ_y (Δ_V 1_x)(y) θ(y) = (Δ_V θ)(x)` by the symmetry of the open graph, so `(Δ_V θ)(x) ∈ ℤ`. -/

open LatticeProb.Percolation Rigidity.Section6 Classical

namespace Rigidity.Proofs.S6

variable {d : ℕ}

/-- `[f] = Σ_x f(x) [1_x]` in the sandpile group. -/
theorem mk_eq_sum_zsmul_chip (ω : Configuration d) (V : Finset (Vertex d)) (f : V → ℤ) :
    (QuotientAddGroup.mk f : SandpileGroup ω V) = ∑ x, f x • Steps.S6.chip ω V x := by
  have hsingle : ∀ x, Pi.single x (f x) = f x • (Pi.single x 1 : V → ℤ) := by
    intro x
    ext y
    by_cases hy : y = x
    · subst hy
      simp
    · simp [hy]
  conv_lhs => rw [← Finset.univ_sum_single f]
  simp only [hsingle, Steps.S6.chip]
  rw [← QuotientAddGroup.mk'_apply, map_sum]
  simp

/-- A character with phases `θ` on the chips takes the value `e^{2πi Σ_x f(x) θ(x)}` at `[f]`. -/
theorem addChar_mk_eq_exp {ω : Configuration d} {V : Finset (Vertex d)}
    {χ : AddChar (SandpileGroup ω V) ℂ} {θ : V → ℝ}
    (hθ : ∀ x, χ (Steps.S6.chip ω V x) = Complex.exp (((2 * Real.pi * θ x : ℝ) : ℂ) * Complex.I))
    (f : V → ℤ) :
    χ (QuotientAddGroup.mk f) =
      Complex.exp (((2 * Real.pi * ∑ x, (f x : ℝ) * θ x : ℝ) : ℂ) * Complex.I) := by
  rw [mk_eq_sum_zsmul_chip, addChar_map_sum_eq_prod]
  simp_rw [AddChar.map_zsmul_eq_zpow, hθ, ← Complex.exp_int_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `Δ_V 1_x = deg(x) 1_x - Σ_{y ∈ V, y ∼ x} 1_y`. -/
theorem toppling_single_apply (ω : Configuration d) (V : Finset (Vertex d)) (x y : V) :
    toppling ω V (Pi.single x 1) y = (if y = x then ((openGraph ω).degree x.val : ℤ) else 0) -
      if (openGraph ω).Adj x.val y.val then 1 else 0 := by
  change ((openGraph ω).degree y.val : ℤ) * (Pi.single x 1 : V → ℤ) y -
    ∑ z : V, (if (openGraph ω).Adj y.val z.val then (Pi.single x 1 : V → ℤ) z else 0) = _
  have hsum : (∑ z : V, if (openGraph ω).Adj y.val z.val then (Pi.single x 1 : V → ℤ) z else 0) =
      if (openGraph ω).Adj x.val y.val then 1 else 0 := by
    rw [Finset.sum_eq_single x (fun z _ hz => by simp [hz]) (by simp)]
    simp [(openGraph ω).adj_comm]
  rw [hsum]
  by_cases hyx : y = x
  · subst hyx
    simp
  · simp [hyx]

/-- `Σ_y (Δ_V 1_x)(y) θ(y) = (Δ_V θ)(x)`, by the symmetry of the open graph. -/
theorem sum_toppling_single_mul (ω : Configuration d) (V : Finset (Vertex d)) (θ : V → ℝ)
    (x : V) :
    ∑ y, ((toppling ω V (Pi.single x 1) y : ℤ) : ℝ) * θ y = Steps.S6.realToppling ω V θ x := by
  simp only [toppling_single_apply, Int.cast_sub, Int.cast_ite, Int.cast_natCast, Int.cast_zero,
    Int.cast_one, sub_mul, ite_mul, zero_mul, one_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Steps.S6.realToppling]

/-- step:6.5-upper, characters: every character of the finite sandpile group is
`[1_x] ↦ e^{2πiθ(x)}` for a phase vector `θ` with `Δ_V θ ∈ ℤ^V`. -/
theorem latticeCorrespondenceStep : Steps.S6.LatticeCorrespondenceStep d := by
  intro ω V hfin χ
  set θ : V → ℝ := fun x => Complex.arg (χ (Steps.S6.chip ω V x)) / (2 * Real.pi) with hθdef
  have hθ : ∀ x, χ (Steps.S6.chip ω V x) =
      Complex.exp (((2 * Real.pi * θ x : ℝ) : ℂ) * Complex.I) := by
    intro x
    have h2 : 2 * Real.pi * θ x = Complex.arg (χ (Steps.S6.chip ω V x)) := by
      rw [hθdef]
      field_simp
    rw [h2]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (χ (Steps.S6.chip ω V x)),
      AddChar.norm_apply χ]
    simp
  refine ⟨θ, hθ, fun x => ?_⟩
  have hker : χ (QuotientAddGroup.mk (toppling ω V (Pi.single x 1))) = 1 := by
    rw [(QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨_, rfl⟩),
      AddChar.map_zero_eq_one]
  rw [addChar_mk_eq_exp hθ, sum_toppling_single_mul] at hker
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hker
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h : ((Steps.S6.realToppling ω V θ x : ℝ) : ℂ) = n := by
    apply mul_right_cancel₀ hpi
    push_cast at hn ⊢
    linear_combination hn
  exact_mod_cast h

end Rigidity.Proofs.S6
