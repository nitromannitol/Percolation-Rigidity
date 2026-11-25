import Rigidity.Proofs.Green.HeatTimeDerivBounds
import LatticeProb.Network.Dirichlet

/-!
# Harmonic replacement and the exit-time function on a finite set

Let `G` be a locally finite graph with degrees at most `D > 0`, `Δ` its Laplacian
`Δf(x) = Σ_{y ∼ x} (f(y) - f(x))` and `A` a finite set of vertices from each of which some vertex
outside `A` is reachable. By the Dirichlet theory of Lattice-Probability
(`LatticeProb.Network.existsUnique_dirichlet`, `interiorLaplacian_surjective` and the minimum
principle) there are

* the harmonic replacement `h` of `g`: `Δh = 0` on `A`, `h = g` off `A`; it satisfies
  `|h| ≤ sup |g|` (`abs_le_of_dirichlet`);
* the exit-time function `e`: `Δe = -1` on `A`, `e = 0` off `A`, `e ≥ 0` (`exists_exitFunction`);

and the comparison `|g - h| ≤ F e` when `|Δg| ≤ F` on `A` (`abs_sub_le_mul_exitFunction`): the
functions `F e ± (g - h)` are superharmonic on `A` and vanish off `A`. (In probabilistic terms `e`
is the expected exit time of the variable speed random walk from `A`, and the comparison is
Dynkin's formula.)

The exit-time function is bounded through the heat kernel `p_t` of the whole graph: if
`Σ_{w ∈ A} p_τ(z, w) ≤ 1/2` for every `z ∈ A`, then `e ≤ 2τ` (`exitFunction_le_two_mul`). Indeed
`ψ(s) = Σ_{w ∈ A} p_s(z, w) e(w) + s` is nondecreasing, since by the summation by parts
`sum_laplacian_mul_eq` its derivative is `Σ_w p_s(z, w) Δe(w) + 1 ≥ -Σ_{w ∈ A} p_s(z, w) + 1 ≥ 0`
(`Δe ≥ 0` off `A`); hence `e(z) = ψ(0) ≤ ψ(τ) ≤ (max e)/2 + τ`. This is the bound
`sup_z E_z τ_A ≤ 2τ` obtained in probability by iterating `P_z(τ_A > τ) ≤ 1/2`.
-/

open scoped Classical
open Finset

namespace Rigidity.Green

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

/-! ### The Laplacian -/

theorem laplacian_lincomb (a b : ℝ) (f g : V → ℝ) (x : V) :
    LatticeProb.Graph.laplacian G (fun v => a * f v + b * g v) x =
      a * LatticeProb.Graph.laplacian G f x + b * LatticeProb.Graph.laplacian G g x := by
  unfold LatticeProb.Graph.laplacian
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem laplacian_sub_apply (f g : V → ℝ) (x : V) :
    LatticeProb.Graph.laplacian G (fun v => f v - g v) x =
      LatticeProb.Graph.laplacian G f x - LatticeProb.Graph.laplacian G g x := by
  unfold LatticeProb.Graph.laplacian
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- `∂_t p_t(z, w) = Δ_w p_t(z, ·)`. -/
theorem heatDeriv_one_eq_laplacian (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (t : ℝ) (z w : V) :
    heatDeriv G D 1 t z w = LatticeProb.Graph.laplacian G (fun u => vsrwHeat G D t z u) w :=
  heatDeriv_succ_right hD hdeg 0 t z w

theorem sum_vsrwHeat_le_one (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    (z : V) (S : Finset V) : ∑ w ∈ S, vsrwHeat G D t z w ≤ 1 :=
  sum_le_hasSum S (fun w _ => vsrwHeat_nonneg hD hdeg ht z w) (hasSum_vsrwHeat hD hdeg ht z)

/-! ### Summation by parts on finite sets -/

/-- Each edge counted from both ends: the double sums over `a ∈ T, b ∼ a` and `b ∈ T, a ∼ b`
agree when `F a b` vanishes unless both ends lie in `T`. -/
theorem sum_sum_neighborFinset_comm (T : Finset V) (F : V → V → ℝ)
    (hF : ∀ a b, G.Adj a b → F a b ≠ 0 → a ∈ T ∧ b ∈ T) :
    ∑ a ∈ T, ∑ b ∈ G.neighborFinset a, F a b = ∑ b ∈ T, ∑ a ∈ G.neighborFinset b, F a b := by
  have h1 : ∀ a ∈ T, ∑ b ∈ G.neighborFinset a, F a b =
      ∑ b ∈ T, if G.Adj a b then F a b else 0 := by
    intro a _
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact (G.mem_neighborFinset a b).2 hb.2
    · intro b hbN hbT
      by_contra hne
      have hadj : G.Adj a b := (G.mem_neighborFinset a b).1 hbN
      exact hbT (Finset.mem_filter.2 ⟨(hF a b hadj hne).2, hadj⟩)
  have h2 : ∀ b ∈ T, ∑ a ∈ G.neighborFinset b, F a b =
      ∑ a ∈ T, if G.Adj a b then F a b else 0 := by
    intro b _
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact (G.mem_neighborFinset b a).2 (G.adj_symm ha.2)
    · intro a haN haT
      by_contra hne
      have hadj : G.Adj a b := G.adj_symm ((G.mem_neighborFinset b a).1 haN)
      exact haT (Finset.mem_filter.2 ⟨(hF a b hadj hne).1, hadj⟩)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]

/-- **Summation by parts**: for `e` vanishing off `S`, `S ⊆ T` and the neighbours of `S` in `T`,
`Σ_{w ∈ S} ΔP(w) e(w) = Σ_{w ∈ T} P(w) Δe(w)`. -/
theorem sum_laplacian_mul_eq {S T : Finset V} (hST : S ⊆ T)
    (hN : ∀ w ∈ S, G.neighborFinset w ⊆ T) (P e : V → ℝ) (he : ∀ w, w ∉ S → e w = 0) :
    ∑ w ∈ S, LatticeProb.Graph.laplacian G P w * e w =
      ∑ w ∈ T, P w * LatticeProb.Graph.laplacian G e w := by
  have hL : ∑ w ∈ S, LatticeProb.Graph.laplacian G P w * e w =
      ∑ w ∈ T, LatticeProb.Graph.laplacian G P w * e w :=
    Finset.sum_subset hST fun w _ hw => by rw [he w hw, mul_zero]
  rw [hL]
  simp only [LatticeProb.Graph.laplacian, Finset.sum_mul, Finset.mul_sum, mul_sub, sub_mul,
    Finset.sum_sub_distrib]
  congr 1
  refine sum_sum_neighborFinset_comm T (fun w u => P u * e w) fun a b hab hne => ?_
  have ha : a ∈ S := by
    by_contra h
    exact hne (by rw [he a h, mul_zero])
  exact ⟨hST ha, hN a ha ((G.mem_neighborFinset a b).2 hab)⟩

/-! ### Dirichlet and Poisson problems -/

variable {A : Finset V}

/-- The harmonic replacement: `Δh = 0` on `A` and `h = g` off `A`. -/
theorem exists_dirichlet (hacc : LatticeProb.Network.BoundaryAccessible G A) (g : V → ℝ) :
    ∃ h : V → ℝ, (∀ x ∈ A, LatticeProb.Graph.laplacian G h x = 0) ∧ ∀ x, x ∉ A → h x = g x := by
  obtain ⟨h, hh, -⟩ := LatticeProb.Network.existsUnique_dirichlet
    (LatticeProb.Network.isCond_unitCond (G := G)) A hacc g
  exact ⟨h, fun x hx => by rw [← LatticeProb.Network.netLaplacian_unitCond]; exact hh.1 x hx,
    hh.2⟩

/-- The Poisson problem: `Δe = f` on `A` and `e = 0` off `A`. -/
theorem exists_poisson (hacc : LatticeProb.Network.BoundaryAccessible G A) (f : V → ℝ) :
    ∃ e : V → ℝ, (∀ x ∈ A, LatticeProb.Graph.laplacian G e x = f x) ∧ ∀ x, x ∉ A → e x = 0 := by
  obtain ⟨u, hu⟩ := LatticeProb.Network.interiorLaplacian_surjective
    (LatticeProb.Network.isCond_unitCond (G := G)) A hacc (fun v => f v.val)
  refine ⟨LatticeProb.Network.extendByZero A u, fun x hx => ?_,
    fun x hx => LatticeProb.Network.extendByZero_apply_of_not_mem u hx⟩
  have := congrFun hu ⟨x, hx⟩
  rw [← LatticeProb.Network.netLaplacian_unitCond]
  exact this

/-- The minimum principle for the Laplacian `Δ`. -/
theorem nonneg_of_laplacian_nonpos (hacc : LatticeProb.Network.BoundaryAccessible G A)
    {φ : V → ℝ} (hφ : ∀ x ∈ A, LatticeProb.Graph.laplacian G φ x ≤ 0)
    (hbd : ∀ x, x ∉ A → 0 ≤ φ x) : ∀ x, 0 ≤ φ x :=
  LatticeProb.Network.superharmonic_minimum_principle
    (LatticeProb.Network.isCond_unitCond (G := G)) A hacc φ 0
    (fun x hx => by rw [LatticeProb.Network.netLaplacian_unitCond]; exact hφ x hx) hbd

/-- The exit-time function: `Δe = -1` on `A`, `e = 0` off `A`, `e ≥ 0`. -/
theorem exists_exitFunction (hacc : LatticeProb.Network.BoundaryAccessible G A) :
    ∃ e : V → ℝ, (∀ x ∈ A, LatticeProb.Graph.laplacian G e x = -1) ∧
      (∀ x, x ∉ A → e x = 0) ∧ ∀ x, 0 ≤ e x := by
  obtain ⟨e, he, he0⟩ := exists_poisson hacc (fun _ => -1)
  refine ⟨e, he, he0, nonneg_of_laplacian_nonpos hacc (fun x hx => ?_) fun x hx => ?_⟩
  · rw [he x hx]; norm_num
  · rw [he0 x hx]

/-- The maximum principle: the harmonic replacement of `g` is bounded by `sup |g|`. -/
theorem abs_le_of_dirichlet (hacc : LatticeProb.Network.BoundaryAccessible G A) {g h : V → ℝ}
    (hh : ∀ x ∈ A, LatticeProb.Graph.laplacian G h x = 0) (hgh : ∀ x, x ∉ A → h x = g x)
    {U : ℝ} (hg : ∀ x, |g x| ≤ U) : ∀ x, |h x| ≤ U := by
  have hp : ∀ σ : ℝ, σ ^ 2 = 1 → ∀ x, 0 ≤ U * 1 + σ * h x := by
    intro σ _
    refine nonneg_of_laplacian_nonpos hacc (φ := fun v => U * 1 + σ * h v) (fun x hx => ?_)
      fun x hx => ?_
    · rw [laplacian_lincomb U σ (fun _ => 1) h x, hh x hx]
      simp [LatticeProb.Graph.laplacian]
    · rw [hgh x hx]
      have := hg x
      rcases abs_le.1 this with ⟨h1, h2⟩
      have hσ : σ = 1 ∨ σ = -1 := by
        have : (σ - 1) * (σ + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; linarith
        · right; linarith
      rcases hσ with rfl | rfl <;> linarith
  intro x
  have h1 := hp 1 (by norm_num) x
  have h2 := hp (-1) (by norm_num) x
  rw [abs_le]
  constructor <;> linarith

/-- **Dynkin's formula, in the form of the comparison principle**: if `h` is the harmonic
replacement of `g` on `A`, `|Δg| ≤ F` on `A` and `e` is the exit-time function, then
`|g - h| ≤ F e`. -/
theorem abs_sub_le_mul_exitFunction (hacc : LatticeProb.Network.BoundaryAccessible G A)
    {g h e : V → ℝ} {F : ℝ} (hh : ∀ x ∈ A, LatticeProb.Graph.laplacian G h x = 0)
    (hgh : ∀ x, x ∉ A → h x = g x) (hLg : ∀ x ∈ A, |LatticeProb.Graph.laplacian G g x| ≤ F)
    (he : ∀ x ∈ A, LatticeProb.Graph.laplacian G e x = -1) (he0 : ∀ x, x ∉ A → e x = 0) :
    ∀ x, |g x - h x| ≤ F * e x := by
  have hp : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ x, 0 ≤ F * e x + σ * (g x - h x) := by
    intro σ hσ
    refine nonneg_of_laplacian_nonpos hacc (φ := fun v => F * e v + σ * (g v - h v))
      (fun x hx => ?_) fun x hx => ?_
    · rw [laplacian_lincomb F σ e (fun v => g v - h v) x, laplacian_sub_apply, he x hx, hh x hx,
        sub_zero]
      have := abs_le.1 (hLg x hx)
      rcases hσ with rfl | rfl <;> linarith
    · rw [he0 x hx, hgh x hx]
      ring_nf
      exact le_refl 0
  intro x
  have h1 := hp 1 (Or.inl rfl) x
  have h2 := hp (-1) (Or.inr rfl) x
  rw [abs_le]
  constructor <;> linarith

/-! ### The bound on the exit-time function -/

/-- `e(z) ≤ Σ_{w ∈ A} p_τ(z, w) e(w) + τ`. -/
theorem exitFunction_le_sum (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {e : V → ℝ}
    (he : ∀ x ∈ A, LatticeProb.Graph.laplacian G e x = -1) (he0 : ∀ x, x ∉ A → e x = 0)
    (hnn : ∀ x, 0 ≤ e x) {τ : ℝ} (hτ : 0 ≤ τ) (z : V) :
    e z ≤ ∑ w ∈ A, vsrwHeat G D τ z w * e w + τ := by
  set T := A ∪ A.biUnion (fun v => G.neighborFinset v) with hT
  have hAT : A ⊆ T := Finset.subset_union_left
  have hNT : ∀ w ∈ A, G.neighborFinset w ⊆ T := fun w hw =>
    (Finset.subset_biUnion_of_mem (fun v => G.neighborFinset v) hw).trans
      Finset.subset_union_right
  let ψ : ℝ → ℝ := fun s => ∑ w ∈ A, vsrwHeat G D s z w * e w + s
  have hderiv : ∀ s, HasDerivAt ψ (∑ w ∈ A, heatDeriv G D 1 s z w * e w + 1) s := fun s =>
    (HasDerivAt.fun_sum fun w _ => (hasDerivAt_heatDeriv hD hdeg 0 s z w).mul_const (e w)).add
      (hasDerivAt_id s)
  have hnonneg : ∀ s, 0 ≤ s → 0 ≤ ∑ w ∈ A, heatDeriv G D 1 s z w * e w + 1 := by
    intro s hs
    have h1 : ∑ w ∈ A, heatDeriv G D 1 s z w * e w =
        ∑ w ∈ T, vsrwHeat G D s z w * LatticeProb.Graph.laplacian G e w := by
      rw [← sum_laplacian_mul_eq hAT hNT (fun u => vsrwHeat G D s z u) e he0]
      exact Finset.sum_congr rfl fun w _ => by rw [heatDeriv_one_eq_laplacian hD hdeg]
    have h2 : ∀ w ∈ T, -(if w ∈ A then vsrwHeat G D s z w else 0) ≤
        vsrwHeat G D s z w * LatticeProb.Graph.laplacian G e w := by
      intro w _
      by_cases hw : w ∈ A
      · rw [if_pos hw, he w hw]; ring_nf; exact le_refl _
      · rw [if_neg hw, neg_zero]
        refine mul_nonneg (vsrwHeat_nonneg hD hdeg hs z w) ?_
        unfold LatticeProb.Graph.laplacian
        exact Finset.sum_nonneg fun u _ => by rw [he0 w hw, sub_zero]; exact hnn u
    have h3 : ∑ w ∈ T, (if w ∈ A then vsrwHeat G D s z w else 0) = ∑ w ∈ A, vsrwHeat G D s z w := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hAT]
    have h4 := Finset.sum_le_sum h2
    rw [Finset.sum_neg_distrib, h3] at h4
    have h5 := sum_vsrwHeat_le_one hD hdeg hs z A
    rw [h1]
    linarith
  have hmono : ψ 0 ≤ ψ τ :=
    le_of_hasDerivAt_nonneg hτ hderiv fun s hs => hnonneg s hs.1
  have hψ0 : ψ 0 = e z := by
    simp only [ψ, vsrwHeat_zero, add_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    by_cases hz : z ∈ A
    · rw [if_pos hz]
    · rw [if_neg hz, he0 z hz]
  rw [← hψ0]
  exact hmono

/-- **The exit-time bound**: if `Σ_{w ∈ A} p_τ(z, w) ≤ 1/2` for every `z ∈ A`, then `e ≤ 2τ`. -/
theorem exitFunction_le_two_mul (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {e : V → ℝ}
    (he : ∀ x ∈ A, LatticeProb.Graph.laplacian G e x = -1) (he0 : ∀ x, x ∉ A → e x = 0)
    (hnn : ∀ x, 0 ≤ e x) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsmall : ∀ z ∈ A, ∑ w ∈ A, vsrwHeat G D τ z w ≤ 1 / 2) : ∀ z, e z ≤ 2 * τ := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · intro z
    rw [he0 z (by rw [hA]; exact Finset.notMem_empty z)]
    linarith
  obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image A e hA
  have hkey := exitFunction_le_sum hD hdeg he he0 hnn hτ z₀
  have hsum : ∑ w ∈ A, vsrwHeat G D τ z₀ w * e w ≤ e z₀ * (1 / 2) := by
    calc ∑ w ∈ A, vsrwHeat G D τ z₀ w * e w ≤ ∑ w ∈ A, vsrwHeat G D τ z₀ w * e z₀ :=
          Finset.sum_le_sum fun w hw =>
            mul_le_mul_of_nonneg_left (hmax w hw) (vsrwHeat_nonneg hD hdeg hτ z₀ w)
      _ = e z₀ * ∑ w ∈ A, vsrwHeat G D τ z₀ w := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ e z₀ * (1 / 2) := mul_le_mul_of_nonneg_left (hsmall z₀ hz₀) (hnn z₀)
  have hz₀τ : e z₀ ≤ 2 * τ := by linarith
  intro z
  by_cases hz : z ∈ A
  · exact (hmax z hz).trans hz₀τ
  · rw [he0 z hz]; linarith

end Rigidity.Green
