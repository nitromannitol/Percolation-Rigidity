import Rigidity.Steps.Section5.MeanZeroRepresentation

/-! # Lemma 5.6, the flow on a finite connected set

On a graph, a function `g` of zero sum supported in a finite set `V` connected through the edges
inside `V` is the divergence `Σ_b F(a, b)` of an antisymmetric vector field `F` carried by the edges
inside `V`, with `|F| ≤ Σ_V |g|`.

Fix a root `r ∈ V` and, for every `c ∈ V`, a path `γ_c` from `c` to `r` inside `V`. The unit flow
`φ_c` of `γ_c` (each traversed oriented edge carries `+1`) is antisymmetric, carried by the edges of
`γ_c`, has divergence `δ_c - δ_r` and is bounded by `1` since a path traverses every edge at most
once. The field `F = Σ_{c ∈ V} g(c) φ_c` has divergence `g - (Σ_V g) δ_r = g`. -/

open Classical

namespace Rigidity.Proofs.Section5

open SimpleGraph

variable {α : Type} {G : SimpleGraph α}

/-- The unit flow of a walk: each oriented edge `(x, y)` traversed by the walk carries `+1` from
`x` to `y` (and `-1` from `y` to `x`). -/
noncomputable def walkFlow : ∀ {u v : α}, G.Walk u v → α → α → ℝ
  | _, _, .nil => fun _ _ => 0
  | u, _, .cons (v := y) _ p => fun a b =>
      ((if a = u ∧ b = y then 1 else 0) - (if a = y ∧ b = u then 1 else 0)) + walkFlow p a b

theorem walkFlow_antisymm {u v : α} (w : G.Walk u v) (a b : α) :
    walkFlow w a b = -walkFlow w b a := by
  induction w with
  | nil => simp [walkFlow]
  | cons h p ih =>
    simp only [walkFlow, ih, and_comm (a := b = _)]
    ring

/-- The unit flow of a walk is carried by the edges of the walk. -/
theorem walkFlow_ne_zero {u v : α} (w : G.Walk u v) {a b : α} (hab : walkFlow w a b ≠ 0) :
    G.Adj a b ∧ a ∈ w.support ∧ b ∈ w.support := by
  induction w with
  | nil => simp [walkFlow] at hab
  | @cons x y z h p ih =>
    simp only [walkFlow] at hab
    by_cases h1 : a = x ∧ b = y
    · obtain ⟨rfl, rfl⟩ := h1
      exact ⟨h, by simp, by simp⟩
    by_cases h2 : a = y ∧ b = x
    · obtain ⟨rfl, rfl⟩ := h2
      exact ⟨h.symm, by simp, by simp⟩
    simp only [h1, h2, if_false, sub_zero, zero_add] at hab
    obtain ⟨hadj, ha, hb⟩ := ih hab
    exact ⟨hadj, by simp [ha], by simp [hb]⟩

/-- The divergence of the unit flow of a walk from `u` to `v` is `δ_u - δ_v`. -/
theorem sum_walkFlow {u v : α} (w : G.Walk u v) {T : Finset α} (hT : ∀ x ∈ w.support, x ∈ T)
    (a : α) : ∑ b ∈ T, walkFlow w a b = (if a = u then 1 else 0) - (if a = v then 1 else 0) := by
  induction w with
  | nil => simp [walkFlow]
  | @cons x y z h p ih =>
    simp only [walkFlow]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ih fun t ht => hT t (by simp [ht])]
    have hy : y ∈ T := hT y (by simp)
    have hx : x ∈ T := hT x (by simp)
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', hx, hy, if_true,
      Finset.sum_const_zero]
    ring

/-- The unit flow of a path is bounded by `1`. -/
theorem abs_walkFlow_le_one {u v : α} (w : G.Walk u v) (hw : w.IsPath) (a b : α) :
    |walkFlow w a b| ≤ 1 := by
  induction w with
  | nil => simp [walkFlow]
  | @cons x y z h p ih =>
    rw [Walk.cons_isPath_iff] at hw
    have hzero : ∀ c, walkFlow p x c = 0 ∧ walkFlow p c x = 0 := fun c =>
      ⟨by_contra fun hc => hw.2 (walkFlow_ne_zero p hc).2.1,
        by_contra fun hc => hw.2 (walkFlow_ne_zero p hc).2.2⟩
    simp only [walkFlow]
    by_cases h1 : a = x ∧ b = y
    · obtain ⟨rfl, rfl⟩ := h1
      simp [h.ne, (hzero b).1]
    by_cases h2 : a = y ∧ b = x
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h.ne, (hzero a).2]
    simpa [h1, h2] using ih hw.1

/-- For `c, r ∈ V` with `V` connected through its own edges, a flow of divergence `δ_c - δ_r`,
carried by the edges inside `V` and bounded by `1`: the unit flow of a path from `c` to `r`
inside `V`. -/
theorem exists_unitFlow {V : Finset α} (hV : (G.induce (V : Set α)).Preconnected) {c r : α}
    (hc : c ∈ V) (hr : r ∈ V) :
    ∃ φ : α → α → ℝ, (∀ a b, φ a b = -φ b a) ∧ (∀ a b, φ a b ≠ 0 → G.Adj a b ∧ a ∈ V ∧ b ∈ V) ∧
      (∀ a, ∑ b ∈ V, φ a b = (if a = c then 1 else 0) - (if a = r then 1 else 0)) ∧
      ∀ a b, |φ a b| ≤ 1 := by
  obtain ⟨w⟩ := hV ⟨c, hc⟩ ⟨r, hr⟩
  have hwV : ∀ x ∈ (w.bypass.map (Embedding.induce (G := G) (V : Set α)).toHom).support,
      x ∈ V := fun x hx => by
    rw [Walk.support_map] at hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact y.2
  obtain ⟨q, hq, hqV⟩ : ∃ q : G.Walk c r, q.IsPath ∧ ∀ x ∈ q.support, x ∈ V :=
    ⟨_, Walk.IsPath.map (Embedding.induce (G := G) (V : Set α)).injective w.bypass_isPath, hwV⟩
  refine ⟨walkFlow q, walkFlow_antisymm q, fun a b hab => ?_, sum_walkFlow q hqV,
    abs_walkFlow_le_one q hq⟩
  obtain ⟨hadj, ha, hb⟩ := walkFlow_ne_zero q hab
  exact ⟨hadj, hqV a ha, hqV b hb⟩

/-- The flow on a finite connected set (corrected draft, proof of Lemma 5.6, L1591-1601; here
carried by paths to a root instead of the gradient of the Neumann problem). -/
theorem flowOnConnectedSet : Steps.Section5.FlowOnConnectedSetStep := by
  intro α G V g hV hg hsum
  have hgV : ∀ a, a ∉ V → g a = 0 := fun a ha => by_contra fun h => ha (hg a h)
  rcases V.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
  · refine ⟨fun _ _ => 0, fun _ _ => by simp, fun _ _ h => absurd rfl h, fun a => ?_,
      fun _ _ => by simp⟩
    simp [hgV a (Finset.notMem_empty a)]
  have hφ : ∀ c, ∃ φ : α → α → ℝ, c ∈ V → (∀ a b, φ a b = -φ b a) ∧
      (∀ a b, φ a b ≠ 0 → G.Adj a b ∧ a ∈ V ∧ b ∈ V) ∧
      (∀ a, ∑ b ∈ V, φ a b = (if a = c then 1 else 0) - (if a = r then 1 else 0)) ∧
      ∀ a b, |φ a b| ≤ 1 := fun c => by
    by_cases hc : c ∈ V
    · obtain ⟨φ, hφ⟩ := exists_unitFlow hV hc hr
      exact ⟨φ, fun _ => hφ⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose φ hφ using hφ
  have hsupp : ∀ a b, (∑ c ∈ V, g c * φ c a b) ≠ 0 → G.Adj a b ∧ a ∈ V ∧ b ∈ V := by
    intro a b hab
    obtain ⟨c, hc, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    exact (hφ c hc).2.1 a b (right_ne_zero_of_mul hne)
  refine ⟨fun a b => ∑ c ∈ V, g c * φ c a b, fun a b => ?_, hsupp, fun a => ?_, fun a b => ?_⟩
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c hc => by rw [(hφ c hc).1 a b, mul_neg]
  · rw [finsum_eq_sum_of_support_subset _ (s := V) fun b hb => (hsupp a b hb).2.2,
      Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun c hc => by rw [(hφ c hc).2.2.1 a]]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_irrel, hsum, Finset.sum_const_zero, ite_self, sub_zero]
    by_cases ha : a ∈ V
    · simp [ha]
    · simp [ha, hgV a ha]
  · calc |∑ c ∈ V, g c * φ c a b| ≤ ∑ c ∈ V, |g c * φ c a b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c ∈ V, |g c| := Finset.sum_le_sum fun c hc => by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) ((hφ c hc).2.2.2 a b)

end Rigidity.Proofs.Section5
