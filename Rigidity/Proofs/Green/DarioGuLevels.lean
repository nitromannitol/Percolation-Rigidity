import Rigidity.Proofs.Green.DarioGuPointwise
import Rigidity.Proofs.Green.DarioGuStepEstimates
import Rigidity.Proofs.Green.DarioGuLatticeSup

/-!
# The statements `H_n` of §4.3 of Dario–Gu and their minimal times

`HeatLevel p σ c k T` is the statement (4.45) at exponent `k` with the lattice family of minimal
times `T`: almost surely, for every `z ∈ 𝒞_∞` and `t ≥ max(1, T z)`, every `x ∈ 𝒞_∞` has
`|p(t, x, z) - θ^{-1} p̄(t, x - z)| ≤ c t^{-k} Φ_c(t, x - z)`. `GoodTimes p T` asks the `T w` to be
measurable, nonnegative and to have a uniform stretched exponential tail; it is stable under the
operations used to build `T¹_par` in (4.44).

This file also proves the estimate of the term (4.48)-b (`density_term_bound`) from
Proposition A.7 at a lattice point near `(x + z)/2` and the Lipschitz bound of `p̄`, and the
existence of the normalized correctors (`exists_isDGCorrector`).
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Green

/-- The statement (4.45) at exponent `k` with minimal times `T`. -/
def HeatLevel (p : unitInterval) (σ c k : ℝ) (T : Vertex 2 → Configuration 2 → ℝ) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∀ z ∈ (uniqueInfiniteComponent h).supp, ∀ t : ℝ, 1 ≤ t → T z ω ≤ t →
      ∀ x ∈ (uniqueInfiniteComponent h).supp,
        |openHeat ω t x z - (theta 2 p)⁻¹ * latticeGaussian σ t x z| ≤
          c * t ^ (-k) * dgPhi c t (latticeDist x z)

/-- A lattice family of minimal times with a uniform stretched exponential tail. -/
def GoodTimes (p : unitInterval) (T : Vertex 2 → Configuration 2 → ℝ) : Prop :=
  (∀ w, Measurable (T w)) ∧ (∀ w ω, 0 ≤ T w ω) ∧
    ∃ C s : ℝ, 2 ≤ C ∧ 0 < s ∧ ∀ w, HasTail p (T w) C s

variable {p : unitInterval}

theorem goodTimes_of_isOsBond {T : Vertex 2 → Configuration 2 → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ : 0 < θ) (hm : ∀ w, Measurable (T w)) (h0 : ∀ w ω, 0 ≤ T w ω)
    (hos : ∀ w, IsOsBond 2 p (T w) s θ) : GoodTimes p T :=
  ⟨hm, h0, max 2 (θ ^ s), s, le_max_left _ _, hs, fun w => hasTail_of_isOsBond hs hθ (hos w)⟩

theorem GoodTimes.max {X Y : Vertex 2 → Configuration 2 → ℝ} (hX : GoodTimes p X)
    (hY : GoodTimes p Y) : GoodTimes p (fun w ω => Max.max (X w ω) (Y w ω)) := by
  obtain ⟨hXm, hX0, CX, sX, hCX, hsX, hXt⟩ := hX
  obtain ⟨hYm, hY0, CY, sY, hCY, hsY, hYt⟩ := hY
  refine ⟨fun w => (hXm w).max (hYm w), fun w ω => le_max_of_le_left (hX0 w ω),
    2 * Max.max CX CY, min sX sY, by linarith [le_max_left CX CY], lt_min hsX hsY, fun w => ?_⟩
  have h1 : HasTail p (X w) (Max.max CX CY) (min sX sY) :=
    ((hXt w).mono (by linarith) (le_max_left _ _)).mono_exponent
      (by linarith [le_max_left CX CY]) (lt_min hsX hsY) (min_le_left _ _)
  have h2 : HasTail p (Y w) (Max.max CX CY) (min sX sY) :=
    ((hYt w).mono (by linarith) (le_max_right _ _)).mono_exponent
      (by linarith [le_max_left CX CY]) (lt_min hsX hsY) (min_le_right _ _)
  exact h1.max h2 (by linarith [le_max_left CX CY])

theorem GoodTimes.rpow {X : Vertex 2 → Configuration 2 → ℝ} (hX : GoodTimes p X) {a : ℝ}
    (ha : 0 < a) : GoodTimes p (fun w ω => X w ω ^ a) := by
  obtain ⟨hXm, hX0, C, s, hC, hs, hXt⟩ := hX
  exact ⟨fun w => (hXm w).pow_const a, fun w ω => Real.rpow_nonneg (hX0 w ω) a, C, s / a, hC,
    div_pos hs ha, fun w => (hXt w).rpow ha (hX0 w)⟩

theorem GoodTimes.const_mul {X : Vertex 2 → Configuration 2 → ℝ} (hX : GoodTimes p X) {c : ℝ}
    (hc : 0 < c) : GoodTimes p (fun w ω => c * X w ω) := by
  obtain ⟨hXm, hX0, C, s, hC, hs, hXt⟩ := hX
  exact ⟨fun w => (hXm w).const_mul c, fun w ω => mul_nonneg hc.le (hX0 w ω),
    Max.max C (c ^ s * C), s, (hC.trans (le_max_left _ _)), hs,
    fun w => (hXt w).const_mul (by linarith) hc⟩

theorem GoodTimes.max_const {X : Vertex 2 → Configuration 2 → ℝ} (hX : GoodTimes p X) {a : ℝ}
    (ha : 0 ≤ a) : GoodTimes p (fun w ω => Max.max (X w ω) a) := by
  obtain ⟨hXm, hX0, C, s, hC, hs, hXt⟩ := hX
  exact ⟨fun w => (hXm w).max measurable_const, fun w ω => le_max_of_le_right ha,
    Max.max C (Max.max 3 (Real.rpow a s)), s, hC.trans (le_max_left _ _), hs,
    fun w => (hXt w).max_const (by linarith) hs⟩

/-- The lattice minimal times of a good family form a good family, and the family is almost surely
bounded. -/
theorem goodTimes_latticeSup {X : Vertex 2 → Configuration 2 → ℝ} (hX : GoodTimes p X) :
    GoodTimes p (fun z ω => latticeSup X z ω) ∧ ∀ z, ∀ᵐ ω ∂latticeBondLaw 2 p,
      BddAbove (Set.range fun w => if latticeDist w z ≤ X w ω + 1 then X w ω else 0) := by
  obtain ⟨hXm, hX0, C, s, hC, hs, hXt⟩ := hX
  obtain ⟨C', hC', h⟩ := hasTail_latticeSup (by linarith) hs hXt
  exact ⟨⟨fun z => measurable_latticeSup hXm z, fun z ω => latticeSup_nonneg hX0 z ω,
    Max.max C' 2, s, le_max_right _ _, hs, fun z => (h z).1.mono hC' (le_max_left _ _)⟩,
    fun z => (h z).2⟩

/-- The normalized correctors of Dario–Gu, §2.3.1, from the qualitative corrector input. -/
theorem exists_isDGCorrector {ω : Configuration 2} {K : OpenComponent ω}
    (hK : ∀ (q : Fin 2 → ℝ) (o : K), ∃! u : K → ℝ, IsCorrectedPlane K q u ∧ u o = 0)
    {z : Vertex 2} (hz : z ∈ K.supp) : ∃ χ : Fin 2 → Vertex 2 → ℝ, IsDGCorrector K z χ := by
  choose u hu using fun k : Fin 2 => (hK (Pi.single k 1) ⟨z, hz⟩).exists
  classical
  refine ⟨fun k x => if hx : x ∈ K.supp then u k ⟨x, hx⟩ + (z k : ℝ) - x k else 0, fun k => ?_⟩
  constructor
  · have key := isCorrectedPlane_add K (hu k).1 (isCorrectedPlane_const K (z k : ℝ))
    rw [add_zero] at key
    convert key using 1
    funext a
    simp only [Pi.add_apply]
    split_ifs with ha
    · rw [Subtype.coe_eta]; ring
    · exact absurd a.2 ha
  · simp [(hu k).2]

/-- Bounded absolute partial sums on `K` give summability and a bound of the series. -/
theorem summable_subtype_of_sum_abs_le {K : Set (Vertex 2)} {f : Vertex 2 → ℝ} {B : ℝ}
    (h : ∀ S : Finset (Vertex 2), (∀ x ∈ S, x ∈ K) → ∑ x ∈ S, |f x| ≤ B) :
    Summable (fun x : K => |f x|) ∧ ∑' x : K, |f x| ≤ B := by
  have hfin : ∀ S : Finset K, ∑ x ∈ S, |f x| ≤ B := by
    intro S
    have hS : ∀ x ∈ S.map (Function.Embedding.subtype _), x ∈ K := by
      intro x hx
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have := h _ hS
    rwa [Finset.sum_map] at this
  have hs : Summable (fun x : K => |f x|) := summable_of_sum_le (fun _ => abs_nonneg _) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

/-- **The term (4.48)-b.** With `m = (x + z)/2`, `p̄(s, x - y) p̄(s, y - z) = p̄(2s, x - z)
p̄(s/2, y - m)`; Proposition A.7 at a lattice point `w` within distance `1` of `m` and the Lipschitz
bound of `p̄` give `|θ^{-1} Σ_{y ∈ K} p̄(s, x - y) p̄(s, y - z) - p̄(2s, x - z)| ≤
p̄(2s, x - z) θ^{-1} (M_L (s/2)^{-1/2} + E)`, where `E` bounds `|Σ_{y ∈ K} p̄(s/2, y - w) - θ|`. -/
theorem density_term_bound {θ σ : ℝ} (hθ : 0 < θ) (hσ : 0 < σ) {ML : ℝ}
    (hLip : ∀ τ : ℝ, 1 ≤ τ → ∀ (m : EuclideanSpace ℝ (Fin 2)) (w : Vertex 2),
      ‖m - latticeEuclideanEmbedding w‖ ≤ 1 → ∀ S : Finset (Vertex 2),
        ∑ y ∈ S, |gaussianHeat σ τ (latticeEuclideanEmbedding y - m) -
          gaussianHeat σ τ (latticeEuclideanEmbedding y - latticeEuclideanEmbedding w)| ≤
            ML * τ ^ (-(1 / 2 : ℝ)))
    (K : Set (Vertex 2)) {s : ℝ} (hs : 2 ≤ s) (x z w : Vertex 2)
    (hw : ‖(1 / 2 : ℝ) • (latticeEuclideanEmbedding x + latticeEuclideanEmbedding z) -
      latticeEuclideanEmbedding w‖ ≤ 1) {E : ℝ}
    (hE : |∑' y : K, latticeGaussian σ (s / 2) y.val w - θ| ≤ E) :
    |θ⁻¹ * ∑' y : K, latticeGaussian σ s x y * latticeGaussian σ s y z -
        latticeGaussian σ (s + s) x z| ≤
      latticeGaussian σ (s + s) x z * θ⁻¹ * (ML * (s / 2) ^ (-(1 / 2 : ℝ)) + E) := by
  have hs0 : 0 < s := by linarith
  have hs2 : 1 ≤ s / 2 := by linarith
  set ex := latticeEuclideanEmbedding x
  set ez := latticeEuclideanEmbedding z
  set ew := latticeEuclideanEmbedding w
  set m := (1 / 2 : ℝ) • (ex + ez) with hm
  have hprod : ∀ y : Vertex 2, latticeGaussian σ s x y * latticeGaussian σ s y z =
      latticeGaussian σ (s + s) x z *
        gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y - m) := by
    intro y
    unfold latticeGaussian
    rw [gaussianHeat_mul_gaussianHeat hσ hs0, show 2 * s = s + s by ring]
    have e1 : (ex - latticeEuclideanEmbedding y) + (latticeEuclideanEmbedding y - ez) = ex - ez := by
      abel
    have e2 : (1 / 2 : ℝ) • ((latticeEuclideanEmbedding y - ez) - (ex - latticeEuclideanEmbedding y)) =
        latticeEuclideanEmbedding y - m := by
      rw [hm]; module
    rw [e1, e2]
  simp_rw [hprod]
  rw [tsum_mul_left]
  set G := latticeGaussian σ (s + s) x z
  have hG : 0 < G := latticeGaussian_pos hσ (by linarith) x z
  -- summability of the two Gaussian sums on `K`
  have hdiff := summable_subtype_of_sum_abs_le (K := K)
    (f := fun y => gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y - m) -
      gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y - ew))
    (fun S _ => hLip (s / 2) hs2 m w hw S)
  have hw' : Summable (fun y : K => latticeGaussian σ (s / 2) y.val w) := by
    have h := summable_subtype_of_sum_abs_le (K := K) (f := fun y => latticeGaussian σ (s / 2) y w)
      (B := (2 * Real.pi * σ * (s / 2))⁻¹ * (4 * Real.exp (1 / (2 * σ) / 2) *
        (1 + 1 / (1 / (2 * σ))) ^ 2 * (s / 2))) (fun S _ => by
        have hsum := sum_exp_neg_sq_div_le (c := 1 / (2 * σ)) (by positivity) hs2 w S
        calc ∑ y ∈ S, |latticeGaussian σ (s / 2) y w|
            = (2 * Real.pi * σ * (s / 2))⁻¹ *
                ∑ y ∈ S, Real.exp (-(1 / (2 * σ) * latticeDist y w ^ 2 / (s / 2))) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              have e : latticeDist y w ^ 2 / (2 * σ * (s / 2)) =
                  1 / (2 * σ) * latticeDist y w ^ 2 / (s / 2) := by field_simp
              rw [abs_of_pos (latticeGaussian_pos hσ (by linarith) y w), latticeGaussian_eq, e]
          _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity))
    exact h.1.of_abs
  have hsplit : ∑' y : K, gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m) =
      ∑' y : K, (gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m) -
        gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - ew)) +
      ∑' y : K, latticeGaussian σ (s / 2) y.val w := by
    rw [← (hdiff.1.of_abs).tsum_add hw']
    exact tsum_congr fun y => by simp only [latticeGaussian]; ring
  have hD : |∑' y : K, (gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m) -
        gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - ew))| ≤
      ML * (s / 2) ^ (-(1 / 2 : ℝ)) :=
    (abs_tsum_le_tsum_abs hdiff.1).trans hdiff.2
  have hθi : 0 < θ⁻¹ := inv_pos.2 hθ
  calc |θ⁻¹ * (G * ∑' y : K, gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m)) - G|
      = G * θ⁻¹ * |∑' y : K, gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m) - θ| := by
        have hθ' : θ ≠ 0 := hθ.ne'
        rw [show θ⁻¹ * (G * ∑' y : K, gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m))
            - G = G * θ⁻¹ * (∑' y : K, gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m)
              - θ) by field_simp]
        rw [abs_mul, abs_of_pos (by positivity : 0 < G * θ⁻¹)]
    _ ≤ G * θ⁻¹ * (ML * (s / 2) ^ (-(1 / 2 : ℝ)) + E) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hsplit]
        calc |∑' y : K, (gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m) -
              gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - ew)) +
              ∑' y : K, latticeGaussian σ (s / 2) y.val w - θ|
            ≤ |∑' y : K, (gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - m) -
              gaussianHeat σ (s / 2) (latticeEuclideanEmbedding y.val - ew))| +
              |∑' y : K, latticeGaussian σ (s / 2) y.val w - θ| := by
              rw [add_sub_assoc]; exact abs_add_le _ _
          _ ≤ _ := add_le_add hD hE

end Rigidity.Green
