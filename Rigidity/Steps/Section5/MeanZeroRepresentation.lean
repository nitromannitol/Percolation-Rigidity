import Rigidity.Steps.Section5.Common
import Rigidity.External.WellConnected

/-! # Lemma 5.6: the mean-zero potential as a sum of Green gradients

Lemma 5.6 (`MeanZeroRepresentationStmt`, corrected draft L1568-1580, proof L1582-1614): almost
surely, on the event `Σ_{𝒞_∞} f = 0`, `u_f(x) = Σ_e F(e) ∇_y G(x, e)` for a finitely supported
antisymmetric vector field `F` on the edges of `𝒞_∞` whose support size and `L²` norm are
`O_s(C_f)` (eq. `estimates-on-F`).

The carving follows the printed proof of Lemma 5.6 with one deviation: the flow `F` is carried
by a spanning tree of a finite connected set containing `supp f ∩ 𝒞_∞` (the flux through a tree
edge is the mass of `f` on one side of it), instead of being the gradient of the solution of the
Neumann problem (eq. `Neumannprob`). This gives `|F| ≤ Σ |f|` pointwise, so the `L²` bound of
eq. `estimates-on-F` follows from the size of the connecting set alone and the Poincaré inequality
on `𝒞_*(□_f)` is not used. The steps:

* `ConnectingSetStep` (from Proposition 2.3, `Rigidity.External.WellConnectedInput`, d = 2):
  almost surely `supp f ∩ 𝒞_∞` lies in a finite subset of `𝒞_∞` connected through its own edges,
  of cardinality at most a random variable `R ≤ O_s(θ)` (in the paper, the cluster `𝒞_*(□_f)` of
  the smallest well-connected box `□_f`, eq. `bound-on-size`);
* `FlowOnConnectedSetStep` (deterministic, any graph): a function `g` of zero sum supported in a
  finite connected set `V` is the divergence `Σ_b F(a, b)` of an antisymmetric `F` carried by the
  edges inside `V`, with `|F| ≤ Σ_V |g|`;
* `SummationByPartsStep` (deterministic, any kernel; discrete divergence theorem): if
  `Σ_b F(a, b) = g(a)` then `Σ_a g(a) k(a) = ½ Σ_{(a, b)} F(a, b) (k(a) - k(b))`.

With `M = Σ |f|`, the field `F` is supported in the `|V|²` oriented pairs of `V`, with `L²` norm
at most `|V|² M`; both are bounded by `X = (M + 1) max(R, 0)² ≤ O_{s/2}((M + 1) θ²)`. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section2 Rigidity.Section5

/-- Step (Proposition 2.3 for `d = 2`, eq. `bound-on-size`): for `p_c < p < 1` and finitely
supported `f`, almost surely `supp f ∩ 𝒞_∞` is contained in a finite set `V ⊆ 𝒞_∞` connected
through the edges of `𝒞_∞` inside `V`, with `|V| ≤ R(ω)` for a measurable `R ≤ O_s(θ)`. -/
def ConnectingSetStep : Prop :=
  Rigidity.External.WellConnectedInput → ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ f : Vertex 2 → ℤ, (Function.support f).Finite →
    ∃ θ s : ℝ, 0 < θ ∧ 0 < s ∧ ∃ R : Configuration 2 → ℝ, Measurable R ∧ IsOs 2 p R s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∃ V : Finset (uniqueInfiniteComponent h),
          ((componentGraph (uniqueInfiniteComponent h)).induce
            (V : Set (uniqueInfiniteComponent h))).Preconnected ∧
          (∀ y : uniqueInfiniteComponent h, f y.val ≠ 0 → y ∈ V) ∧ (V.card : ℝ) ≤ R ω

/-- Step (flow on a finite connected set; deterministic): on a graph, a function `g` of zero sum
supported in a finite set `V` connected through the edges inside `V` is the divergence
`Σ_b F(a, b)` of an antisymmetric `F` carried by the edges inside `V`, with `|F| ≤ Σ_V |g|`
(the flux through the edges of a spanning tree of `V`). -/
def FlowOnConnectedSetStep : Prop :=
  ∀ {α : Type} (G : SimpleGraph α) (V : Finset α) (g : α → ℝ),
    (G.induce (V : Set α)).Preconnected → (∀ a, g a ≠ 0 → a ∈ V) → ∑ a ∈ V, g a = 0 →
    ∃ F : α → α → ℝ, (∀ a b, F a b = -F b a) ∧
      (∀ a b, F a b ≠ 0 → G.Adj a b ∧ a ∈ V ∧ b ∈ V) ∧
      (∀ a, ∑ᶠ b, F a b = g a) ∧ ∀ a b, |F a b| ≤ ∑ c ∈ V, |g c|

/-- Step (summation by parts, the discrete divergence theorem; any kernel): if an antisymmetric
`F` supported in a finite set `S` of oriented pairs has divergence `Σ_b F(a, b) = g(a)`, then
`Σ_a g(a) k(a) = ½ Σ_{(a, b) ∈ S} F(a, b) (k(a) - k(b))` for every `k`. -/
def SummationByPartsStep : Prop :=
  ∀ {α : Type} (F : α → α → ℝ) (g : α → ℝ) (S : Finset (α × α)),
    (∀ a b, F a b = -F b a) → (∀ a b, F a b ≠ 0 → (a, b) ∈ S) → (∀ a, ∑ᶠ b, F a b = g a) →
    ∀ k : α → ℝ, ∑ᶠ a, g a * k a = (1 / 2) * ∑ e ∈ S, F e.1 e.2 * (k e.1 - k e.2)

/-- If `R ≤ O_s(θ)` then `c max(R, 0)² ≤ O_{s/2}(c θ²)` for `c > 0`: the two integrands agree. -/
theorem isOs_mul_sq {p : unitInterval} {R : Configuration 2 → ℝ} {s θ c : ℝ} (hθ : 0 < θ)
    (hc : 0 < c) (hR : IsOs 2 p R s θ) :
    IsOs 2 p (fun ω => c * max (R ω) 0 ^ 2) (s / 2) (c * θ ^ 2) := by
  have key : ∀ ω, Real.rpow (max (c * max (R ω) 0 ^ 2 / (c * θ ^ 2)) 0) (s / 2) =
      Real.rpow (max (R ω / θ) 0) s := by
    intro ω
    have h0 : 0 ≤ max (R ω) 0 / θ := div_nonneg (le_max_right _ _) hθ.le
    have h1 : c * max (R ω) 0 ^ 2 / (c * θ ^ 2) = (max (R ω) 0 / θ) ^ 2 := by
      rw [div_pow]; field_simp
    have h2 : max (R ω / θ) 0 = max (R ω) 0 / θ := by
      rw [← max_div_div_right hθ.le, zero_div]
    rw [h1, max_eq_left (sq_nonneg _), h2, Real.rpow_eq_pow, Real.rpow_eq_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul h0]
    congr 1
    push_cast
    ring
  unfold IsOs at hR ⊢
  simp only [key]
  exact hR

/-- Lemma 5.6 follows from the uniqueness of the infinite cluster, the connecting set given by
Proposition 2.3, the flow on a finite connected set and summation by parts. -/
theorem meanZeroRepresentation_of_steps {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hW : Rigidity.External.WellConnectedInput) (hU : UniqueClusterAe p)
    (hC : ConnectingSetStep) (hF : FlowOnConnectedSetStep) (hS : SummationByPartsStep)
    (f : Vertex 2 → ℤ) : MeanZeroRepresentationStmt p f := by
  intro hf
  obtain ⟨θ, s, hθ, hs, R, hRm, hRos, hRae⟩ := hC hW p hpc hp1 f hf
  obtain ⟨M, hM, hfM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |(f y : ℝ)| ≤ M := by
    refine ⟨∑ y ∈ hf.toFinset, |(f y : ℝ)|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
      fun y => ?_⟩
    by_cases hy : f y = 0
    · simp only [hy, Int.cast_zero, abs_zero]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact Finset.single_le_sum (f := fun y => |(f y : ℝ)|) (fun _ _ => abs_nonneg _)
        (hf.mem_toFinset.mpr hy)
  have hM1 : 0 < M + 1 := by linarith
  refine ⟨(M + 1) * θ ^ 2, s / 2, mul_pos hM1 (pow_pos hθ 2), half_pos hs,
    fun ω => (M + 1) * max (R ω) 0 ^ 2,
    measurable_const.mul ((hRm.max measurable_const).pow_const 2), isOs_mul_sq hθ hM1 hRos, ?_⟩
  filter_upwards [hU, hRae] with ω hω hV
  refine ⟨hω, fun hm => ?_⟩
  obtain ⟨V, hVc, hVf, hVR⟩ := hV hω
  have hsum : ∑ y ∈ V, (f y.val : ℝ) = 0 := by
    have h1 : mass (uniqueInfiniteComponent hω) f = ∑ y ∈ V, f y.val :=
      finsum_eq_sum_of_support_subset _ fun y hy => Finset.mem_coe.mpr (hVf y hy)
    have h2 : ∑ y ∈ V, f y.val = 0 := h1 ▸ hm
    exact_mod_cast h2
  obtain ⟨F, hanti, hsupp, hdiv, hbd⟩ := hF (componentGraph (uniqueInfiniteComponent hω)) V
    (fun y => (f y.val : ℝ)) hVc (fun y hy => hVf y (Int.cast_ne_zero.mp hy)) hsum
  have hSF : ∀ a b, F a b ≠ 0 → (a, b) ∈ V ×ˢ V := fun a b h =>
    Finset.mem_product.mpr ⟨(hsupp a b h).2.1, (hsupp a b h).2.2⟩
  have hn : (V.card : ℝ) ≤ max (R ω) 0 := hVR.trans (le_max_left _ _)
  have hn2 : (V.card : ℝ) ^ 2 ≤ max (R ω) 0 ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hn 2
  have hFb : ∀ a b, |F a b| ≤ V.card * M := fun a b =>
    (hbd a b).trans <| (Finset.sum_le_sum fun c _ => hfM c.val).trans (by simp)
  have hcard : ((V ×ˢ V).card : ℝ) = (V.card : ℝ) ^ 2 := by
    rw [Finset.card_product]; push_cast; ring
  refine ⟨F, hanti, fun a b h => (hsupp a b h).1, V ×ˢ V, hSF, ?_, ?_, ?_⟩
  · rw [hcard]
    exact hn2.trans (le_mul_of_one_le_left (sq_nonneg _) (by linarith))
  · rw [Real.sqrt_le_left (mul_nonneg hM1.le (sq_nonneg _))]
    calc ∑ e ∈ V ×ˢ V, F e.1 e.2 ^ 2 ≤ ∑ _e ∈ V ×ˢ V, ((V.card : ℝ) * M) ^ 2 :=
          Finset.sum_le_sum fun e _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hFb _ _) 2
      _ = ((V.card : ℝ) ^ 2 * M) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
      _ ≤ ((M + 1) * max (R ω) 0 ^ 2) ^ 2 := by
          apply pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) hM)
          nlinarith [mul_le_mul_of_nonneg_right hn2 hM, sq_nonneg (max (R ω) 0)]
  · intro G _ x
    exact hS F _ (V ×ˢ V) hanti hSF hdiv (G x)

end Rigidity.Steps.Section5
