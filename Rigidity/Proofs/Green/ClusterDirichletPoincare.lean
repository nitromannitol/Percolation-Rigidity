import Rigidity.Proofs.Green.DarioGuPoincareHolds
import Rigidity.Proofs.Green.ClusterParabolicEnergy

/-!
# The Poincaré inequality for functions vanishing on the boundary of a ball of the planar cluster

The second part of Proposition 2.7 of Dario–Gu (lines 991-993 of the source), for `p = 2` and
`d = 2`: for `R ≥ M_Poinc(y)` and every function `u` on `𝒞_∞ ∩ B_R(y)` vanishing on the boundary,
`‖u‖_{L̲²(𝒞_∞ ∩ B_R(y))} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_R(y))}`. It is the inequality used in Step 2 of the
proof of Theorem 5 (line 1420) for functions of `C_0^a(𝒞_∞ ∩ B_r)`.

The statement here (`ClusterDirichletPoincareTwo`, proved as `clusterDirichletPoincareTwo_holds`)
asks `u` to vanish only on `∂_a V = V \ int_a(V)`, `V = 𝒞_∞ ∩ B_R(y)`, the points with an open edge
leaving `V`; this set is contained in the boundary `∂(ℤ² ∩ B_R(y)) ∩ 𝒞_∞` of the source, so the
statement implies the printed one. The gradient is over the open edges inside `V` (`gradEnergy`).

Proof: the extension `ũ` of `u` by `0` has the same gradient energy on the larger ball
`𝒞_∞ ∩ B_{24KR}(y)` as `u` on `V` (`gradEnergy_extend_eq`), because every open edge leaving `V`
starts at a point of `∂_a V`; the weak Poincaré inequality (`clusterPoincareTwo_holds`) on
`𝒞_∞ ∩ B_{KR}(y)` bounds `Σ (ũ - m)²`, and the mean `m` is controlled since `ũ = 0` on at least half
of `𝒞_∞ ∩ B_{KR}(y)` when `K` is large (the density lower bound of Proposition A.1,
`clusterDensityInputFaithful_of_concentration`).
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.Cluster Rigidity.Proofs.S2

namespace Rigidity.Green

/-- **Dario–Gu, Proposition 2.7, second part** (`p = 2`, dimension two), for functions vanishing
on `∂_a(𝒞_∞ ∩ B_R(y))`, unnormalized (both sides carry the factor `|𝒞_∞ ∩ B_R(y)|^{-1}` in the
source). -/
def ClusterDirichletPoincareTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ y : Vertex 2,
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ R : ℝ, M ω ≤ R →
          ∀ u : Vertex 2 → ℝ,
            (∀ x ∈ clusterBall (uniqueInfiniteComponent h) y R,
              x ∉ openInterior ω (clusterBall (uniqueInfiniteComponent h) y R) → u x = 0) →
            ∑ x ∈ clusterBall (uniqueInfiniteComponent h) y R, u x ^ 2 ≤
              (C * R) ^ 2 * gradEnergy ω (clusterBall (uniqueInfiniteComponent h) y R) u

/-- The extension of `u` by zero outside `V`. -/
noncomputable def extendZero (V : Finset (Vertex 2)) (u : Vertex 2 → ℝ) (x : Vertex 2) : ℝ := by
  classical
  exact if x ∈ V then u x else 0

/-- **The gradient energy of the extension by zero**: if `u` vanishes on `∂_a V` and `V ⊆ W`, the
extension by zero has the same energy on `W` as `u` on `V`. -/
theorem gradEnergy_extend_eq (ω : Configuration 2) {V W : Finset (Vertex 2)} (hVW : V ⊆ W)
    {u : Vertex 2 → ℝ} (hu : ∀ x ∈ V, x ∉ openInterior ω V → u x = 0) :
    gradEnergy ω W (extendZero V u) = gradEnergy ω V u := by
  classical
  have hedge : ∀ x z, (openGraph ω).Adj x z →
      |extendZero V u z - extendZero V u x| = if z ∈ V ∧ x ∈ V then |u z - u x| else 0 := by
    intro x z hxz
    unfold extendZero
    by_cases hz : z ∈ V <;> by_cases hx : x ∈ V
    · simp [hz, hx]
    · have hz0 : u z = 0 := hu z hz fun hi => hx (hi.2 x hxz.symm)
      simp [hz, hx, hz0]
    · have hx0 : u x = 0 := hu x hx fun hi => hz (hi.2 z hxz)
      simp [hz, hx, hx0]
    · simp [hz, hx]
  have hinner : ∀ x ∈ W, ∑ z ∈ W.filter (fun z => (openGraph ω).Adj x z),
      |extendZero V u z - extendZero V u x| =
        if x ∈ V then ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), |u z - u x| else 0 := by
    intro x _
    rw [Finset.sum_congr rfl fun z hz => hedge x z (Finset.mem_filter.1 hz).2]
    by_cases hx : x ∈ V
    · rw [if_pos hx, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext z
      simp only [Finset.mem_filter, hx, and_true]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hVW h.1, h.2⟩, h.1⟩⟩
    · rw [if_neg hx]
      exact Finset.sum_eq_zero fun z _ => by simp [hx]
  unfold gradEnergy
  rw [Finset.sum_congr rfl fun x hx => by rw [hinner x hx]]
  have : ∀ x ∈ W, (if x ∈ V then ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z),
      |u z - u x| else 0) ^ 2 = if x ∈ V then (∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z),
      |u z - u x|) ^ 2 else 0 := fun x _ => by split_ifs <;> simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 hVW]

/-- **The deterministic step**: if `V ⊆ W ⊆ W'`, `2 |V| ≤ |W|`, `u` vanishes on `∂_a V` and the
weak Poincaré inequality `(Σ_W (ũ - (ũ)_W)² / |W|)^{1/2} ≤ C ρ (E_{W'}(ũ) / |W'|)^{1/2}` holds for
the extension `ũ` by zero, then `Σ_V u² ≤ 6 C² ρ² E_V(u)`. -/
theorem sum_sq_le_of_weakPoincare (ω : Configuration 2) {V W W' : Finset (Vertex 2)}
    (hVW : V ⊆ W) (hWW' : W ⊆ W') (hcard : 2 * (V.card : ℝ) ≤ W.card) {u : Vertex 2 → ℝ}
    (hu : ∀ x ∈ V, x ∉ openInterior ω V → u x = 0) {C ρ : ℝ}
    (hP : Real.sqrt ((∑ x ∈ W, (extendZero V u x - finAvg W (extendZero V u)) ^ 2) / W.card) ≤
      C * ρ * Real.sqrt (gradEnergy ω W' (extendZero V u) / W'.card)) :
    ∑ x ∈ V, u x ^ 2 ≤ 6 * C ^ 2 * ρ ^ 2 * gradEnergy ω V u := by
  classical
  rcases W.eq_empty_or_nonempty with hW | hWne
  · have hV : V = ∅ := Finset.subset_empty.1 (hW ▸ hVW)
    rw [hV, Finset.sum_empty]
    exact mul_nonneg (by positivity) (gradEnergy_nonneg ω _ u)
  have hcW : (0 : ℝ) < W.card := by exact_mod_cast hWne.card_pos
  have hcW' : (W.card : ℝ) ≤ W'.card := by exact_mod_cast Finset.card_le_card hWW'
  have hcW'0 : (0 : ℝ) < W'.card := lt_of_lt_of_le hcW hcW'
  set ũ := extendZero V u with hũ
  set m := finAvg W ũ with hm
  set S := ∑ x ∈ W, (ũ x - m) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set G := gradEnergy ω V u with hG
  have hG0 : 0 ≤ G := gradEnergy_nonneg ω V u
  have hE : gradEnergy ω W' ũ = G := gradEnergy_extend_eq ω (hVW.trans hWW') hu
  -- the weak Poincaré inequality, squared
  have hSle : S ≤ C ^ 2 * ρ ^ 2 * G := by
    rw [hE] at hP
    have h1 : S / W.card ≤ (C * ρ) ^ 2 * (G / W'.card) := by
      have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hP 2
      rw [Real.sq_sqrt (div_nonneg hS0 hcW.le), mul_pow, Real.sq_sqrt (div_nonneg hG0 hcW'0.le)]
        at hsq
      exact hsq
    have h2 : (C * ρ) ^ 2 * (G / W'.card) ≤ (C * ρ) ^ 2 * (G / W.card) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hG0 hcW hcW') (sq_nonneg _)
    have h3 : S / W.card ≤ (C * ρ) ^ 2 * G / W.card := by
      have := h1.trans h2
      rwa [mul_div_assoc]
    rw [div_le_div_iff_of_pos_right hcW] at h3
    nlinarith [h3]
  -- the mean
  have hout : ((W \ V).card : ℝ) * m ^ 2 ≤ S := by
    have h1 : ∑ x ∈ W \ V, (ũ x - m) ^ 2 = ((W \ V).card : ℝ) * m ^ 2 := by
      rw [Finset.sum_congr rfl fun x hx => by
        rw [hũ, extendZero, if_neg (Finset.mem_sdiff.1 hx).2, zero_sub, neg_sq]]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => sq_nonneg _
  have hcard' : (W.card : ℝ) ≤ 2 * ((W \ V).card : ℝ) := by
    have := Finset.card_sdiff_add_card_eq_card hVW
    have h' : ((W \ V).card : ℝ) + V.card = W.card := by exact_mod_cast this
    linarith
  have hmS : (W.card : ℝ) * m ^ 2 ≤ 2 * S := by nlinarith [sq_nonneg m]
  -- the sum over `V`
  have hV : ∑ x ∈ V, u x ^ 2 = ∑ x ∈ W, ũ x ^ 2 := by
    rw [← Finset.sum_subset hVW fun x _ hx => by rw [hũ, extendZero, if_neg hx]; ring]
    exact Finset.sum_congr rfl fun x hx => by rw [hũ, extendZero, if_pos hx]
  have hW2 : ∑ x ∈ W, ũ x ^ 2 ≤ 2 * S + 2 * ((W.card : ℝ) * m ^ 2) := by
    have : ∑ x ∈ W, ũ x ^ 2 ≤ ∑ x ∈ W, (2 * (ũ x - m) ^ 2 + 2 * m ^ 2) :=
      Finset.sum_le_sum fun x _ => by nlinarith [sq_nonneg (ũ x - 2 * m)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at this
    linarith
  rw [hV]
  nlinarith

end Rigidity.Green
