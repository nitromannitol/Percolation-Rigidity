import Rigidity.Steps.S6.SlowMixing
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# The `L²` distance of the sandpile chain in terms of its eigenvalues

Step `step:6.5-fourier` (paper L2855-2858 of the corrected draft; Jerison-Levine-Pike, Lemma 2.9).
On a finite abelian group `G`, Plancherel's identity reads
`|G| Σ_g |f(g)|² = Σ_χ |Σ_g f(g) χ(g)|²` (`card_mul_sum_sq_eq_sum_norm_sq`). The law after `t`
steps of the walk started at `s` with steps uniform over `c(x)`, `x ∈ ι`, has Fourier coefficient
`χ(s) λ_χ^t` at `χ`, with `λ_χ = |ι|⁻¹ Σ_x χ(c(x))` (`sum_card_filter_mul_apply`). Applied to
`f = P^t - 1/|G|` on the sandpile group, the coefficient vanishes at `χ = 1` and has modulus
`|λ_χ|^t` elsewhere, since `|χ(s)| = 1`.
-/

open Rigidity.Section6 Rigidity.Steps.S6 ComplexConjugate

namespace Rigidity.Proofs.S6

section FiniteAbelian

variable {G : Type*} [AddCommGroup G]

/-- A character sends a finite sum to the product of its values. -/
lemma addChar_map_sum_eq_prod {ι : Type*} (χ : AddChar G ℂ) (s : Finset ι) (f : ι → G) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

variable [Fintype G]

/-- Plancherel's identity on a finite abelian group, for a real function. -/
theorem card_mul_sum_sq_eq_sum_norm_sq (f : G → ℝ) :
    (Fintype.card G : ℝ) * ∑ g, f g ^ 2 = ∑ χ : AddChar G ℂ, ‖∑ g, (f g : ℂ) * χ g‖ ^ 2 := by
  classical
  have key : ∀ χ : AddChar G ℂ, ((‖∑ g, (f g : ℂ) * χ g‖ ^ 2 : ℝ) : ℂ) =
      ∑ g, ∑ h, (f g : ℂ) * f h * χ (g - h) := by
    intro χ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
    rw [map_mul, Complex.conj_ofReal, sub_eq_add_neg, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_conj]
    ring
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Finset.sum_congr rfl fun χ _ => key χ]
  calc ((Fintype.card G : ℝ) * ∑ g, f g ^ 2 : ℝ)
      = ∑ g, ∑ h, (f g : ℂ) * f h * ∑ χ : AddChar G ℂ, χ (g - h) := by
        simp_rw [AddChar.sum_apply_eq_ite, sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        push_cast
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => by ring
    _ = ∑ χ : AddChar G ℂ, ∑ g, ∑ h, (f g : ℂ) * f h * χ (g - h) := by
        simp_rw [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Finset.sum_comm

/-- The Fourier coefficient at `χ` of the (unnormalized) law after `t` steps of the walk started
at `s` with steps `c(x)`, `x ∈ ι`: `Σ_g #{w : s + Σ_k c(w_k) = g} χ(g) = χ(s) (Σ_x χ(c(x)))^t`. -/
theorem sum_card_filter_mul_apply [DecidableEq G] {ι : Type*} [Fintype ι] (s : G) (c : ι → G)
    (t : ℕ) (χ : AddChar G ℂ) :
    ∑ g, ((Finset.univ.filter fun w : Fin t → ι => s + ∑ k, c (w k) = g).card : ℂ) * χ g =
      χ s * (∑ x, χ (c x)) ^ t := by
  calc _ = ∑ w : Fin t → ι, χ (s + ∑ k, c (w k)) := by
        simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
        rw [Finset.sum_comm]
        simp
    _ = ∑ w : Fin t → ι, χ s * ∏ k, χ (c (w k)) := by
        simp_rw [AddChar.map_add_eq_mul, addChar_map_sum_eq_prod]
    _ = χ s * (∑ x, χ (c x)) ^ t := by
        rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (_ : Fin t) x => χ (c x)), Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]

end FiniteAbelian

/-- step:6.5-fourier (paper L2855-2858; Jerison-Levine-Pike, Lemma 2.9):
`‖P^t - U‖₂² = Σ_{χ ≠ 1} |λ_χ|^{2t}` for the sandpile chain on a finite sandpile group. -/
theorem fourierStep {d : ℕ} : FourierStep d := by
  intro ω V hV hfin t
  classical
  letI : Fintype (SandpileGroup ω V) := Fintype.ofFinite _
  set s : SandpileGroup ω V :=
    QuotientAddGroup.mk (fun x : V => ((LatticeProb.Percolation.openGraph ω).degree x.val : ℤ) - 1)
    with hs
  have hm : (V.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hV.card_pos.ne'
  have hN : (Fintype.card (SandpileGroup ω V) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hlaw : ∀ χ : AddChar (SandpileGroup ω V) ℂ,
      ∑ g, (chainLaw ω V t g : ℂ) * χ g = χ s * chainEigenvalue ω V χ ^ t := by
    intro χ
    have h := sum_card_filter_mul_apply s (chip ω V) t χ
    calc ∑ g, (chainLaw ω V t g : ℂ) * χ g
        = ((V.card : ℂ) ^ t)⁻¹ * ∑ g, ((Finset.univ.filter fun w : Fin t → V =>
            s + ∑ k, chip ω V (w k) = g).card : ℂ) * χ g := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [chainLaw, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
            Complex.ofReal_natCast, div_eq_inv_mul, mul_assoc]
          rfl
      _ = χ s * chainEigenvalue ω V χ ^ t := by
          rw [h, chainEigenvalue, mul_pow, inv_pow]
          ring
  have hhat : ∀ χ : AddChar (SandpileGroup ω V) ℂ,
      ‖∑ g, ((chainLaw ω V t g - 1 / (Fintype.card (SandpileGroup ω V) : ℝ) : ℝ) : ℂ) * χ g‖ ^ 2
        = if χ ≠ 1 then ‖chainEigenvalue ω V χ‖ ^ (2 * t) else 0 := by
    intro χ
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
      sub_mul, Finset.sum_sub_distrib, hlaw, ← Finset.mul_sum, AddChar.sum_eq_ite]
    by_cases hχ : χ = 1
    · subst hχ
      have h1 : chainEigenvalue ω V 1 = 1 := by
        simp [chainEigenvalue, hm]
      simp [h1, ← AddChar.one_eq_zero, hN]
    · rw [if_pos hχ, if_neg (by rwa [← AddChar.one_eq_zero]), mul_zero, sub_zero, norm_mul,
        AddChar.norm_apply, one_mul, norm_pow, ← pow_mul, mul_comm]
  unfold l2DistSq
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, card_mul_sum_sq_eq_sum_norm_sq]
  simp_rw [finsum_eq_if]
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun χ _ => by exact_mod_cast hhat χ

end Rigidity.Proofs.S6
