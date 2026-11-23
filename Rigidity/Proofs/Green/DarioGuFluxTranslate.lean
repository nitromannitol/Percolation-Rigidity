import Rigidity.Proofs.Green.DarioGuFluxInput

/-!
# The translated flux of Remark B.3 of Dario–Gu

The term `ξ` of the equation (4.25)-(4.26) of `w` involves the translated flux
`[g̃*_{e_k}]_i = T_{-e_i} [g̃_{e_k}]_i`, and Remark B.3 of Dario–Gu (lines 3165-3186 of the source)
asserts that its `H̲^{-1}`-norm on `𝒞_∞ ∩ B_r(y)` is also at most `C r^α` ("the proof is identical
to the proof of Proposition B.1 and the details are left to the reader"). This file deduces it
from the bound on `g̃_{e_k}` (Proposition 2.13) and a bound `L` on the flux `a(Dχ_{e_k} + e_k)`
on the edges of the ball: for `v ∈ C_0^a(V)`,
`Σ_V [g̃*]_i v - Σ_V [g̃]_i v = Σ_{x, x + e_i ∈ V} a(Dχ + e_k)_i(x) (v(x + e_i) - v(x))`, since the
terms of the edges leaving `V` vanish (`sum_edgeFlux_shift_sub_le`), and the right side is at most
`L Σ_V |∇v| ≤ L |V| ‖v‖_{H̲¹(V)}` (`weakNormLe_translatedFlux`).
-/

open scoped Classical
open LatticeProb.Percolation

namespace Rigidity.Green

/-- The flux `[a(Dχ_{e_k} + e_k)]_i` on the edge `{x, x + e_i}`. -/
noncomputable def edgeFlux (ω : Configuration 2) (χ : Fin 2 → Vertex 2 → ℝ) (k i : Fin 2)
    (x : Vertex 2) : ℝ :=
  if (openGraph ω).Adj x (x + Pi.single i 1) then
    (if i = k then 1 else 0) + (χ k (x + Pi.single i 1) - χ k x) else 0

theorem centeredFlux_eq_edgeFlux (ω : Configuration 2) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ)
    (k i : Fin 2) (x : Vertex 2) :
    centeredFlux ω σ χ k i x = edgeFlux ω χ k i x - σ / 2 * (if i = k then 1 else 0) := rfl

theorem translatedFlux_eq_edgeFlux (ω : Configuration 2) (σ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ)
    (k i : Fin 2) (x : Vertex 2) :
    translatedFlux ω σ χ k i x =
      edgeFlux ω χ k i (x - Pi.single i 1) - σ / 2 * (if i = k then 1 else 0) := by
  unfold translatedFlux edgeFlux
  rw [sub_add_cancel]

theorem openGradNorm_nonneg (ω : Configuration 2) (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ)
    (x : Vertex 2) : 0 ≤ openGradNorm ω V v x :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- One open edge `{x, x + e_i}` inside `V` contributes to `|∇v|(x)`. -/
theorem abs_sub_le_openGradNorm {ω : Configuration 2} {V : Finset (Vertex 2)}
    {v : Vertex 2 → ℝ} {x : Vertex 2} {i : Fin 2}
    (hadj : (openGraph ω).Adj x (x + Pi.single i 1)) (hV : x + Pi.single i 1 ∈ V) :
    |v (x + Pi.single i 1) - v x| ≤ openGradNorm ω V v x := by
  have hmem : x + Pi.single i 1 ∈ LatticeProb.nbrFinset x :=
    LatticeProb.Graph.Zd.mem_nbrFinset.2 ⟨i, Or.inl rfl⟩
  have hsum := Finset.single_le_sum (s := LatticeProb.nbrFinset x)
    (f := fun z => if (openGraph ω).Adj x z ∧ z ∈ V then |v z - v x| else 0)
    (fun z _ => ite_nonneg (abs_nonneg _) le_rfl) hmem
  rw [if_pos (And.intro hadj hV)] at hsum
  exact hsum

/-- The translation of the flux changes its pairing with `v ∈ C_0^a(V)` by at most
`L Σ_V |∇v|`, where `L` bounds the flux on the edges of `V`. -/
theorem sum_edgeFlux_shift_sub_le {ω : Configuration 2} {V : Finset (Vertex 2)}
    {χ : Fin 2 → Vertex 2 → ℝ} {k i : Fin 2} {L : ℝ}
    (hA : ∀ x ∈ V, |edgeFlux ω χ k i x| ≤ L) {v : Vertex 2 → ℝ}
    (hv : ∀ x ∈ V, x ∉ openInterior ω V → v x = 0) :
    ∑ x ∈ V, edgeFlux ω χ k i (x - Pi.single i 1) * v x - ∑ x ∈ V, edgeFlux ω χ k i x * v x ≤
      L * ∑ x ∈ V, openGradNorm ω V v x := by
  set e : Vertex 2 := Pi.single i 1 with he
  set A := edgeFlux ω χ k i with hAdef
  have h1 : ∀ x ∈ V, x - e ∉ V → A (x - e) * v x = 0 := by
    intro x hx hxe
    by_cases hadj : (openGraph ω).Adj (x - e) x
    · have : x ∉ openInterior ω V := fun hint => hxe (hint.2 _ hadj.symm)
      rw [hv x hx this, mul_zero]
    · rw [hAdef, edgeFlux, he, sub_add_cancel, if_neg hadj, zero_mul]
  have h2 : ∀ x ∈ V, x + e ∉ V → A x * v x = 0 := by
    intro x hx hxe
    by_cases hadj : (openGraph ω).Adj x (x + e)
    · have : x ∉ openInterior ω V := fun hint => hxe (hint.2 _ hadj)
      rw [hv x hx this, mul_zero]
    · rw [hAdef, edgeFlux, if_neg hadj, zero_mul]
  have s1 : ∑ x ∈ V, A (x - e) * v x =
      ∑ x ∈ V.filter (fun x => x - e ∈ V), A (x - e) * v x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    split_ifs with h
    · rfl
    · exact h1 x hx h
  have s2 : ∑ x ∈ V, A x * v x = ∑ x ∈ V.filter (fun x => x + e ∈ V), A x * v x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    split_ifs with h
    · rfl
    · exact h2 x hx h
  have s3 : ∑ x ∈ V.filter (fun x => x - e ∈ V), A (x - e) * v x =
      ∑ x ∈ V.filter (fun x => x + e ∈ V), A x * v (x + e) := by
    refine Finset.sum_nbij' (fun x => x - e) (fun x => x + e) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, by rw [sub_add_cancel]; exact hx.1⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, by rw [add_sub_cancel_right]; exact hx.1⟩
    · intro x _
      exact sub_add_cancel x e
    · intro x _
      exact add_sub_cancel_right x e
    · intro x _
      rw [sub_add_cancel]
  rw [s1, s2, s3, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hterm : ∀ x ∈ V.filter (fun x => x + e ∈ V),
      A x * v (x + e) - A x * v x ≤ L * openGradNorm ω V v x := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hL : 0 ≤ L := (abs_nonneg _).trans (hA x hx.1)
    by_cases hadj : (openGraph ω).Adj x (x + e)
    · calc A x * v (x + e) - A x * v x = A x * (v (x + e) - v x) := by ring
        _ ≤ |A x * (v (x + e) - v x)| := le_abs_self _
        _ = |A x| * |v (x + e) - v x| := abs_mul _ _
        _ ≤ L * openGradNorm ω V v x :=
            mul_le_mul (hA x hx.1) (abs_sub_le_openGradNorm hadj hx.2) (abs_nonneg _) hL
    · have hA0 : A x = 0 := by rw [hAdef, edgeFlux, if_neg hadj]
      rw [hA0, zero_mul, zero_mul, sub_zero]
      exact mul_nonneg hL (openGradNorm_nonneg ω V v x)
  calc ∑ x ∈ V.filter (fun x => x + e ∈ V), (A x * v (x + e) - A x * v x)
      ≤ ∑ x ∈ V.filter (fun x => x + e ∈ V), L * openGradNorm ω V v x :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ x ∈ V, L * openGradNorm ω V v x := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro x hx _
        exact mul_nonneg ((abs_nonneg _).trans (hA x hx)) (openGradNorm_nonneg ω V v x)

/-- `|V|^{-1} Σ_V |∇v| ≤ ‖v‖_{H̲¹(V)}`. -/
theorem inv_card_mul_sum_openGradNorm_le (ω : Configuration 2) (V : Finset (Vertex 2))
    (v : Vertex 2 → ℝ) :
    (V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNorm ω V v x ≤ clusterH1Norm ω V v := by
  have hfirst : 0 ≤ (V.card : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.sqrt ((V.card : ℝ)⁻¹ * ∑ x ∈ V, v x ^ 2) := by positivity
  have hS0 : 0 ≤ ∑ x ∈ V, openGradNorm ω V v x :=
    Finset.sum_nonneg fun x _ => openGradNorm_nonneg ω V v x
  have hcs : (V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNorm ω V v x ≤
      Real.sqrt ((V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNorm ω V v x ^ 2) := by
    rcases Nat.eq_zero_or_pos V.card with h0 | hpos
    · rw [h0, Nat.cast_zero, inv_zero, zero_mul]
      exact Real.sqrt_nonneg _
    · have hc : (0 : ℝ) < V.card := Nat.cast_pos.2 hpos
      apply Real.le_sqrt_of_sq_le
      have h := sq_sum_le_card_mul_sum_sq (s := V) (f := fun x => openGradNorm ω V v x)
      calc ((V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNorm ω V v x) ^ 2
          = (V.card : ℝ)⁻¹ * ((V.card : ℝ)⁻¹ * (∑ x ∈ V, openGradNorm ω V v x) ^ 2) := by ring
        _ ≤ (V.card : ℝ)⁻¹ * ((V.card : ℝ)⁻¹ *
            ((V.card : ℝ) * ∑ x ∈ V, openGradNorm ω V v x ^ 2)) := by gcongr
        _ = (V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNorm ω V v x ^ 2 := by
            field_simp
  unfold clusterH1Norm
  linarith

/-- **Dario–Gu, Remark B.3** (deterministic part): if `‖[g̃_{e_k}]_i‖_{H̲^{-1}(V)} ≤ B` and the
flux `[a(Dχ_{e_k} + e_k)]_i` is at most `L` on `V`, then `‖[g̃*_{e_k}]_i‖_{H̲^{-1}(V)} ≤ B + L`. -/
theorem weakNormLe_translatedFlux {ω : Configuration 2} {V : Finset (Vertex 2)} {σ : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {k i : Fin 2} {B L : ℝ}
    (h : WeakNormLe ω V (centeredFlux ω σ χ k i) B)
    (hA : ∀ x ∈ V, |edgeFlux ω χ k i x| ≤ L) (hL : 0 ≤ L) :
    WeakNormLe ω V (translatedFlux ω σ χ k i) (B + L) := by
  intro v hv
  have hk := h v hv
  have hkey := sum_edgeFlux_shift_sub_le hA hv
  have hgrad := inv_card_mul_sum_openGradNorm_le ω V v
  have hc : 0 ≤ (V.card : ℝ)⁻¹ := by positivity
  have e : ∑ x ∈ V, translatedFlux ω σ χ k i x * v x =
      ∑ x ∈ V, centeredFlux ω σ χ k i x * v x +
        (∑ x ∈ V, edgeFlux ω χ k i (x - Pi.single i 1) * v x -
          ∑ x ∈ V, edgeFlux ω χ k i x * v x) := by
    simp only [translatedFlux_eq_edgeFlux, centeredFlux_eq_edgeFlux, sub_mul,
      Finset.sum_sub_distrib]
    ring
  rw [e, mul_add, add_mul]
  have h3 : (V.card : ℝ)⁻¹ * (∑ x ∈ V, edgeFlux ω χ k i (x - Pi.single i 1) * v x -
      ∑ x ∈ V, edgeFlux ω χ k i x * v x) ≤ L * clusterH1Norm ω V v := by
    calc (V.card : ℝ)⁻¹ * (∑ x ∈ V, edgeFlux ω χ k i (x - Pi.single i 1) * v x -
          ∑ x ∈ V, edgeFlux ω χ k i x * v x)
        ≤ (V.card : ℝ)⁻¹ * (L * ∑ x ∈ V, openGradNorm ω V v x) :=
          mul_le_mul_of_nonneg_left hkey hc
      _ = L * ((V.card : ℝ)⁻¹ * ∑ x ∈ V, openGradNorm ω V v x) := by ring
      _ ≤ L * clusterH1Norm ω V v := mul_le_mul_of_nonneg_left hgrad hL
  linarith

end Rigidity.Green
