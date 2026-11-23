import LatticeProb.Prob.UpdateSite
import LatticeProb.Prob.EfronSteinSigma
import LatticeProb.Prob.IndepPi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.CondVar

/-!
# Conditional expectations under the product Bernoulli law

For an index type `ι` and `p ∈ [0, 1]`, `bernProd ι p` is the product of Bernoulli laws of
parameter `p` on `ι → Bool`. For a set `A` of coordinates, `coordSigma A` is the σ-algebra of the
coordinates in `A`, and `allExcept e` the σ-algebra of the coordinates other than `e` (the
σ-algebra `F(𝓑_d \ {e})` of Dario, Proposition 2.17, when `ι` is the set of lattice bonds).

* `indep_coordSigma`: coordinates in disjoint sets are independent;
* `condExp_allExcept_ae_eq`: `E[X | F(other coordinates)] = p X(ω^{e,1}) + (1 - p) X(ω^{e,0})`,
  where `ω^{e,b}` is `ω` with the coordinate `e` set to `b`;
* `condExp_allExcept_condExp_ae_eq`, `condExp_condExp_allExcept_ae_eq`: for `e ∈ S`, conditioning
  on `F(S)` and on `F(other coordinates than e)` in either order gives `E[X | F(S \ {e})]`;
  hence (`vertical_condExp_ae_eq`) the vertical derivative of `E[X | F(S)]` in `e` is the
  conditional expectation on `F(S)` of the vertical derivative of `X`, and it vanishes for
  `e ∉ S`.
-/

namespace Rigidity.Probability

open MeasureTheory ProbabilityTheory

variable {ι : Type*}

/-- The product of Bernoulli laws of parameter `p` on `ι → Bool`. -/
noncomputable def bernProd (ι : Type*) (p : unitInterval) : Measure (ι → Bool) :=
  Measure.infinitePi fun _ : ι => bernoulliMeasure true false p

instance (p : unitInterval) : IsProbabilityMeasure (bernProd ι p) := by
  unfold bernProd
  infer_instance

/-- The σ-algebra of the coordinates in `A`. -/
abbrev coordSigma (A : Set ι) : MeasurableSpace (ι → Bool) :=
  ⨆ i ∈ A, MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance

/-- The σ-algebra `F(ι \ {e})` of the coordinates other than `e`. -/
abbrev allExcept (e : ι) : MeasurableSpace (ι → Bool) :=
  MeasurableSpace.comap (fun (ω : ι → Bool) (b : {b : ι // b ≠ e}) => ω b) inferInstance

theorem comap_eval_le (i : ι) :
    MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance ≤
      (inferInstance : MeasurableSpace (ι → Bool)) :=
  (measurable_pi_apply i).comap_le

theorem coordSigma_le (A : Set ι) : coordSigma A ≤ (inferInstance : MeasurableSpace (ι → Bool)) :=
  iSup₂_le fun i _ => comap_eval_le i

theorem coordSigma_mono {A B : Set ι} (h : A ⊆ B) : coordSigma A ≤ coordSigma B :=
  iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ B) =>
    MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance) i (h hi)

theorem coordSigma_union (A B : Set ι) : coordSigma (A ∪ B) = coordSigma A ⊔ coordSigma B :=
  iSup_union

theorem allExcept_eq (e : ι) : allExcept e = coordSigma ({e}ᶜ : Set ι) := by
  rw [allExcept, LatticeProb.comap_pi_eq_iSup (fun (b : {b : ι // b ≠ e}) (ω : ι → Bool) => ω b)]
  refine le_antisymm (iSup_le fun b => ?_) (iSup₂_le fun i hi => ?_)
  · exact le_iSup₂ (f := fun i (_ : i ∈ ({e}ᶜ : Set ι)) =>
      MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance) b.1 b.2
  · exact le_iSup (fun b : {b : ι // b ≠ e} =>
      MeasurableSpace.comap (fun ω : ι → Bool => ω b) inferInstance) ⟨i, hi⟩

theorem allExcept_le (e : ι) : allExcept e ≤ (inferInstance : MeasurableSpace (ι → Bool)) := by
  rw [allExcept_eq]; exact coordSigma_le _

theorem comap_restrict_eq (S : Finset ι) :
    MeasurableSpace.comap (S.restrict : (ι → Bool) → (S → Bool)) inferInstance =
      coordSigma (S : Set ι) := by
  rw [show (S.restrict : (ι → Bool) → (S → Bool)) = fun ω (i : S) => ω i from rfl,
    LatticeProb.comap_pi_eq_iSup (fun (i : S) (ω : ι → Bool) => ω i)]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun i hi => ?_)
  · exact le_iSup₂ (f := fun i (_ : i ∈ (S : Set ι)) =>
      MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance) i.1 i.2
  · exact le_iSup (fun i : S =>
      MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance) ⟨i, hi⟩

theorem iIndep_coord (p : unitInterval) :
    iIndep (fun i => MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance)
      (bernProd ι p) := by
  have h := iIndepFun_infinitePi (P := fun _ : ι => bernoulliMeasure true false p)
    (X := fun _ (b : Bool) => b) (fun _ => measurable_id)
  exact (iIndepFun_iff_iIndep (fun _ => inferInstance) _ _).1 h

/-- Coordinates in disjoint sets are independent. -/
theorem indep_coordSigma (p : unitInterval) {A B : Set ι} (h : Disjoint A B) :
    Indep (coordSigma A) (coordSigma B) (bernProd ι p) :=
  indep_iSup_of_disjoint comap_eval_le (iIndep_coord p) h

end Rigidity.Probability
