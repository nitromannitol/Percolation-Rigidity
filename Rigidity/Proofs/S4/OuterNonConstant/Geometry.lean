import Rigidity.Proofs.S4.OuterNonConstant.Defs

/-!
# Lemma 4.8, conditional form: the geometry of `Q_R`

Deterministic lattice facts about the objects of `Defs.lean`: the face sites, the inner neighbour,
the connector bonds (cardinality, position, connecting all face sites), and the two branches
(`chainBonds (highWaypoints d R)` and `chainBonds (lowWaypoints hd R w)`).
-/

namespace Rigidity.Proofs.S4.OuterNonConstant

open LatticeProb LatticeProb.Percolation LatticeProb.Network
  LatticeProb.Network.OpenLadder.Embedding Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-! ### Lattice adjacency -/

theorem adj_coords {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    ∃ k, (∀ j, j ≠ k → y j = x j) ∧ (y k = x k + 1 ∨ y k = x k - 1) := by
  obtain ⟨k, hk⟩ := Graph.Zd.adj_iff.mp h
  refine ⟨k, fun j hj => ?_, ?_⟩
  · rcases hk with rfl | rfl <;> simp [unit, hj]
  · rcases hk with rfl | rfl <;> simp [unit]

theorem adj_of_coords {x y : Vertex d} (k : Fin d) (hj : ∀ j, j ≠ k → y j = x j)
    (h : y k = x k + 1 ∨ y k = x k - 1) : (nearestNeighborGraph d).Adj x y := by
  refine Graph.Zd.adj_iff.mpr ⟨k, ?_⟩
  rcases h with h | h
  · left
    funext j
    by_cases hjk : j = k
    · subst hjk; simp [unit, h]
    · simp [unit, hjk, hj j hjk]
  · right
    funext j
    by_cases hjk : j = k
    · subst hjk; simp [unit, h]
    · simp [unit, hjk, hj j hjk]

/-! ### Regions -/

theorem sign_sub_of_abs {z : ℤ} {R : ℕ} (hR : 1 ≤ R) (hz : |z| = R) :
    (z = R ∧ z - Int.sign z = (R : ℤ) - 1) ∨ (z = -(R : ℤ) ∧ z - Int.sign z = -(R : ℤ) + 1) := by
  rcases (abs_eq (Nat.cast_nonneg R)).mp hz with h | h
  · left; refine ⟨h, ?_⟩; rw [Int.sign_eq_one_of_pos (by omega)]; omega
  · right; refine ⟨h, ?_⟩; rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega

theorem innerNeighbor_apply_ne {R : ℕ} {x : Vertex d} {i : Fin d}
    (hj : ∀ j, j ≠ i → |x j| < R) {k : Fin d} (hk : k ≠ i) : innerNeighbor R x k = x k := by
  have := hj k hk
  simp [innerNeighbor, this.ne]

theorem innerNeighbor_apply_self {R : ℕ} {x : Vertex d} {i : Fin d} (hi : |x i| = R) :
    innerNeighbor R x i = x i - Int.sign (x i) := by
  simp [innerNeighbor, hi]

/-- G1 -/
theorem mem_cube_of_mem_faceSites {R : ℕ} {x : Vertex d} (hx : x ∈ faceSites d R) :
    x ∈ cube d R := by
  obtain ⟨i, hi, hj⟩ := hx
  intro k
  by_cases hk : k = i
  · subst hk; exact hi.le
  · exact (hj k hk).le

/-- G2 -/
theorem not_mem_cube_pred_of_mem_faceSites {R : ℕ} {x : Vertex d} (hR : 1 ≤ R)
    (hx : x ∈ faceSites d R) : x ∉ cube d (R - 1) := by
  intro hc
  obtain ⟨i, hi, -⟩ := hx
  have h1 := abs_le.mp (hc i)
  have h2 := (abs_eq (Nat.cast_nonneg R)).mp hi
  omega

/-- G3 -/
theorem mem_cube_pred_or_faceSites_of_adj {R : ℕ} {x y : Vertex d} (hR : 1 ≤ R)
    (hx : x ∈ cube d (R - 1)) (hxy : (nearestNeighborGraph d).Adj x y) :
    y ∈ cube d (R - 1) ∨ y ∈ faceSites d R := by
  obtain ⟨k, hk, hk'⟩ := adj_coords hxy
  have hxk := abs_le.mp (hx k)
  by_cases hyk : |y k| ≤ ((R - 1 : ℕ) : ℤ)
  · left
    intro j
    by_cases hj : j = k
    · subst hj; exact hyk
    · rw [hk j hj]; exact hx j
  · right
    refine ⟨k, ?_, fun j hj => ?_⟩
    · rw [abs_le] at hyk
      rw [abs_eq (Nat.cast_nonneg R)]
      omega
    · rw [hk j hj]
      have := abs_le.mp (hx j)
      rw [abs_lt]
      omega

/-- G4 -/
theorem adj_innerNeighbor {R : ℕ} {x : Vertex d} (hR : 1 ≤ R) (hx : x ∈ faceSites d R) :
    (nearestNeighborGraph d).Adj x (innerNeighbor R x) := by
  obtain ⟨i, hi, hj⟩ := hx
  refine adj_of_coords i (fun j hji => innerNeighbor_apply_ne hj hji) ?_
  rw [innerNeighbor_apply_self hi]
  rcases sign_sub_of_abs hR hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- G5 -/
theorem innerNeighbor_mem_cube {R : ℕ} {x : Vertex d} (hR : 1 ≤ R) (hx : x ∈ faceSites d R) :
    innerNeighbor R x ∈ cube d (R - 1) := by
  obtain ⟨i, hi, hj⟩ := hx
  intro k
  by_cases hk : k = i
  · subst hk
    rw [innerNeighbor_apply_self hi, abs_le]
    rcases sign_sub_of_abs hR hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rw [innerNeighbor_apply_ne hj hk, abs_le]
    have := abs_lt.mp (hj k hk)
    constructor <;> omega

/-- G6 -/
theorem eq_innerNeighbor_of_adj {R : ℕ} {x y : Vertex d} (hR : 1 ≤ R) (hx : x ∈ faceSites d R)
    (hy : y ∈ cube d (R - 1)) (hxy : (nearestNeighborGraph d).Adj x y) :
    y = innerNeighbor R x := by
  obtain ⟨i, hi, hj⟩ := hx
  obtain ⟨k, hk, hk'⟩ := adj_coords hxy
  have hki : k = i := by
    by_contra hne
    have h1 := hk i (Ne.symm hne)
    have h2 := abs_le.mp (hy i)
    have h3 := (abs_eq (Nat.cast_nonneg R)).mp hi
    rw [h1] at h2
    omega
  subst hki
  funext j
  by_cases hji : j = k
  · subst hji
    rw [innerNeighbor_apply_self hi]
    have h2 := abs_le.mp (hy j)
    rcases sign_sub_of_abs hR hi with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> omega
  · rw [innerNeighbor_apply_ne hj hji, hk j hji]

theorem adj_update {x : Vertex d} (j : Fin d) {v : ℤ} (h : v = x j + 1 ∨ v = x j - 1) :
    (nearestNeighborGraph d).Adj x (Function.update x j v) :=
  adj_of_coords j (fun k hk => Function.update_of_ne hk _ _) (by rwa [Function.update_self])

theorem update_face_props {R : ℕ} {x : Vertex d} {i j : Fin d} (hji : j ≠ i)
    (hi : |x i| = R) (hx : ∀ k, k ≠ i → k ≠ j → |x k| < R) {v : ℤ} (hv : |v| < R) :
    |Function.update x j v i| = R ∧ ∀ k, k ≠ i → |Function.update x j v k| < R := by
  refine ⟨?_, fun k hk => ?_⟩
  · rwa [Function.update_of_ne (Ne.symm hji)]
  · rcases eq_or_ne k j with rfl | hkj
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hkj]; exact hx k hk hkj

theorem update_mem_faceSites {R : ℕ} {x : Vertex d} {i j : Fin d} (hji : j ≠ i)
    (hi : |x i| = R) (hx : ∀ k, k ≠ i → k ≠ j → |x k| < R) {v : ℤ} (hv : |v| < R) :
    Function.update x j v ∈ faceSites d R :=
  ⟨i, (update_face_props hji hi hx hv).1, (update_face_props hji hi hx hv).2⟩

theorem exists_other (hd : 2 ≤ d) (i : Fin d) : ∃ j : Fin d, j ≠ i := by
  by_cases h : i.val = 0
  · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
  · exact ⟨⟨0, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩

/-- G7 -/
theorem exists_adj_faceSites (hd : 2 ≤ d) {R : ℕ} {x : Vertex d} (hR : 2 ≤ R)
    (hx : x ∈ faceSites d R) : ∃ y ∈ faceSites d R, (nearestNeighborGraph d).Adj x y := by
  obtain ⟨i, hi, hj⟩ := hx
  obtain ⟨j, hji⟩ := exists_other hd i
  have hxj := abs_lt.mp (hj j hji)
  by_cases hlt : x j < (R : ℤ) - 1
  · exact ⟨_, update_mem_faceSites hji hi (fun k hk _ => hj k hk) (v := x j + 1) (abs_lt.mpr ⟨by omega, by omega⟩),
      adj_update j (Or.inl rfl)⟩
  · exact ⟨_, update_mem_faceSites hji hi (fun k hk _ => hj k hk) (v := x j - 1) (abs_lt.mpr ⟨by omega, by omega⟩),
      adj_update j (Or.inr rfl)⟩

/-- G8 -/
theorem finite_faceSites {R : ℕ} : (faceSites d R).Finite :=
  (cube_finite d R).subset fun _ hx => mem_cube_of_mem_faceSites hx

/-! ### Connector bonds -/

theorem abs_sign_mul {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (a : ℤ) : |σ * a| = |a| := by
  rcases hσ with rfl | rfl <;> simp

theorem edgeSite_self (R : ℕ) (i j : Fin d) (σ τ : ℤ) : edgeSite R i j σ τ i = σ * R := by
  simp [edgeSite]

theorem edgeSite_other {R : ℕ} {i j : Fin d} (hij : i ≠ j) (σ τ : ℤ) :
    edgeSite R i j σ τ j = τ * R := by
  simp [edgeSite, Ne.symm hij]

theorem edgeSite_ne {R : ℕ} {i j k : Fin d} (hki : k ≠ i) (hkj : k ≠ j) (σ τ : ℤ) :
    edgeSite R i j σ τ k = 0 := by
  simp [edgeSite, hki, hkj]

theorem abs_edgeSite_self {R : ℕ} {i j : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (τ : ℤ) :
    |edgeSite R i j σ τ i| = R := by
  rw [edgeSite_self, abs_sign_mul hσ]; simp

theorem abs_edgeSite_other {R : ℕ} {i j : Fin d} (hij : i ≠ j) (σ : ℤ) {τ : ℤ}
    (hτ : τ = 1 ∨ τ = -1) : |edgeSite R i j σ τ j| = R := by
  rw [edgeSite_other hij, abs_sign_mul hτ]; simp

theorem abs_sub_one_lt {R : ℕ} (hR : 1 ≤ R) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    |σ * ((R : ℤ) - 1)| < R := by
  rw [abs_sign_mul hσ, abs_lt]; constructor <;> omega

theorem edgeSite_mem_cube {R : ℕ} {i j : Fin d} {σ τ : ℤ} (hij : i ≠ j) (hσ : σ = 1 ∨ σ = -1)
    (hτ : τ = 1 ∨ τ = -1) : edgeSite R i j σ τ ∈ cube d R := by
  intro k
  by_cases hki : k = i
  · subst hki; exact (abs_edgeSite_self hσ τ).le
  · by_cases hkj : k = j
    · subst hkj; exact (abs_edgeSite_other hij σ hτ).le
    · rw [edgeSite_ne hki hkj]; simp

theorem not_mem_cube_pred_edgeSite {R : ℕ} (hR : 1 ≤ R) {i j : Fin d} {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) : edgeSite R i j σ τ ∉ cube d (R - 1) := by
  intro hc
  have h1 := abs_le.mp (hc i)
  have h2 := (abs_eq (Nat.cast_nonneg R)).mp (abs_edgeSite_self (R := R) (i := i) (j := j) hσ τ)
  omega

theorem update_first_props {R : ℕ} (hR : 1 ≤ R) {i j : Fin d} {σ τ : ℤ} (hij : i ≠ j)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    |Function.update (edgeSite R i j σ τ) j (τ * ((R : ℤ) - 1)) i| = R ∧
      ∀ k, k ≠ i → |Function.update (edgeSite R i j σ τ) j (τ * ((R : ℤ) - 1)) k| < R :=
  update_face_props (Ne.symm hij) (abs_edgeSite_self hσ τ)
    (fun k hki hkj => by rw [edgeSite_ne hki hkj]; simp; omega) (abs_sub_one_lt hR hτ)

theorem update_second_props {R : ℕ} (hR : 1 ≤ R) {i j : Fin d} {σ τ : ℤ} (hij : i ≠ j)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    |Function.update (edgeSite R i j σ τ) i (σ * ((R : ℤ) - 1)) j| = R ∧
      ∀ k, k ≠ j → |Function.update (edgeSite R i j σ τ) i (σ * ((R : ℤ) - 1)) k| < R :=
  update_face_props hij (abs_edgeSite_other hij σ hτ)
    (fun k hkj hki => by rw [edgeSite_ne hki hkj]; simp; omega) (abs_sub_one_lt hR hσ)

theorem update_first_mem_faceSites {R : ℕ} (hR : 1 ≤ R) {i j : Fin d} {σ τ : ℤ} (hij : i ≠ j)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    Function.update (edgeSite R i j σ τ) j (τ * ((R : ℤ) - 1)) ∈ faceSites d R :=
  ⟨i, (update_first_props hR hij hσ hτ).1, (update_first_props hR hij hσ hτ).2⟩

theorem update_second_mem_faceSites {R : ℕ} (hR : 1 ≤ R) {i j : Fin d} {σ τ : ℤ} (hij : i ≠ j)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    Function.update (edgeSite R i j σ τ) i (σ * ((R : ℤ) - 1)) ∈ faceSites d R :=
  ⟨j, (update_second_props hR hij hσ hτ).1, (update_second_props hR hij hσ hτ).2⟩

/-- G10 -/
theorem mem_cube_of_mem_connectorBonds {R : ℕ} {e : Bond d} (hR : 1 ≤ R)
    (he : e ∈ connectorBonds d R) : ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R := by
  obtain ⟨i, j, hij, σ, τ, hσ, hτ, h | h⟩ := he <;> intro z hz <;> rw [h, Sym2.mem_iff] at hz <;>
    rcases hz with rfl | rfl
  · exact edgeSite_mem_cube hij hσ hτ
  · exact mem_cube_of_mem_faceSites (update_first_mem_faceSites hR hij hσ hτ)
  · exact edgeSite_mem_cube hij hσ hτ
  · exact mem_cube_of_mem_faceSites (update_second_mem_faceSites hR hij hσ hτ)

/-- G11 -/
theorem exists_faceSite_of_mem_connectorBonds {R : ℕ} {e : Bond d} (hR : 2 ≤ R)
    (he : e ∈ connectorBonds d R) : ∃ z ∈ (e : Sym2 (Vertex d)), z ∈ faceSites d R := by
  obtain ⟨i, j, hij, σ, τ, hσ, hτ, h | h⟩ := he
  · exact ⟨_, by rw [h]; exact Sym2.mem_mk_right _ _, update_first_mem_faceSites (by omega) hij hσ hτ⟩
  · exact ⟨_, by rw [h]; exact Sym2.mem_mk_right _ _, update_second_mem_faceSites (by omega) hij hσ hτ⟩

/-- G12 -/
theorem not_mem_cube_pred_of_mem_connectorBonds {R : ℕ} {e : Bond d} (hR : 2 ≤ R)
    (he : e ∈ connectorBonds d R) : ∀ z ∈ (e : Sym2 (Vertex d)), z ∉ cube d (R - 1) := by
  obtain ⟨i, j, hij, σ, τ, hσ, hτ, h | h⟩ := he <;> intro z hz <;> rw [h, Sym2.mem_iff] at hz <;>
    rcases hz with rfl | rfl
  · exact not_mem_cube_pred_edgeSite (by omega) hσ
  · exact not_mem_cube_pred_of_mem_faceSites (by omega) (update_first_mem_faceSites (by omega) hij hσ hτ)
  · exact not_mem_cube_pred_edgeSite (by omega) hσ
  · exact not_mem_cube_pred_of_mem_faceSites (by omega) (update_second_mem_faceSites (by omega) hij hσ hτ)

/-- The connector bond with the given parameters, as an unordered pair of sites. -/
def connectorPair (R : ℕ) (p : Fin d × Fin d × Bool × Bool × Bool) : Sym2 (Vertex d) :=
  if p.2.2.2.2 then
    s(edgeSite R p.1 p.2.1 (if p.2.2.1 then 1 else -1) (if p.2.2.2.1 then 1 else -1),
      Function.update (edgeSite R p.1 p.2.1 (if p.2.2.1 then 1 else -1)
        (if p.2.2.2.1 then 1 else -1)) p.2.1
        ((if p.2.2.2.1 then 1 else -1) * ((R : ℤ) - 1)))
  else
    s(edgeSite R p.1 p.2.1 (if p.2.2.1 then 1 else -1) (if p.2.2.2.1 then 1 else -1),
      Function.update (edgeSite R p.1 p.2.1 (if p.2.2.1 then 1 else -1)
        (if p.2.2.2.1 then 1 else -1)) p.1 ((if p.2.2.1 then 1 else -1) * ((R : ℤ) - 1)))

theorem connectorBonds_val_subset (R : ℕ) :
    Subtype.val '' connectorBonds d R ⊆ Set.range (connectorPair R) := by
  rintro _ ⟨e, ⟨i, j, hij, σ, τ, hσ, hτ, h | h⟩, rfl⟩
  · refine ⟨(i, j, decide (σ = 1), decide (τ = 1), true), ?_⟩
    have hσ' : (if decide (σ = 1) = true then (1 : ℤ) else -1) = σ := by
      rcases hσ with rfl | rfl <;> simp
    have hτ' : (if decide (τ = 1) = true then (1 : ℤ) else -1) = τ := by
      rcases hτ with rfl | rfl <;> simp
    simp only [connectorPair, hσ', hτ', if_true]
    exact h.symm
  · refine ⟨(i, j, decide (σ = 1), decide (τ = 1), false), ?_⟩
    have hσ' : (if decide (σ = 1) = true then (1 : ℤ) else -1) = σ := by
      rcases hσ with rfl | rfl <;> simp
    have hτ' : (if decide (τ = 1) = true then (1 : ℤ) else -1) = τ := by
      rcases hτ with rfl | rfl <;> simp
    simp only [connectorPair, hσ', hτ', Bool.false_eq_true, if_false]
    exact h.symm

/-- G9, finiteness -/
theorem finite_connectorBonds {R : ℕ} : (connectorBonds d R).Finite := by
  have : (Subtype.val '' connectorBonds d R).Finite :=
    (Set.finite_range (connectorPair R)).subset (connectorBonds_val_subset R)
  exact Set.Finite.of_finite_image this Subtype.val_injective.injOn

/-- G9, cardinality -/
theorem ncard_connectorBonds_le {R : ℕ} : (connectorBonds d R).ncard ≤ 8 * d ^ 2 := by
  have h1 : (connectorBonds d R).ncard = (Subtype.val '' connectorBonds d R).ncard :=
    (Set.ncard_image_of_injective _ Subtype.val_injective).symm
  have h2 : (Subtype.val '' connectorBonds d R).ncard ≤ (Set.range (connectorPair R)).ncard :=
    Set.ncard_le_ncard (connectorBonds_val_subset R) (Set.finite_range _)
  have h3 : (Set.range (connectorPair (d := d) R)).ncard ≤
      (Set.univ : Set (Fin d × Fin d × Bool × Bool × Bool)).ncard := by
    rw [← Set.image_univ]
    exact Set.ncard_image_le (Set.toFinite _)
  rw [Set.ncard_univ] at h3
  have h4 : Nat.card (Fin d × Fin d × Bool × Bool × Bool) = 8 * d ^ 2 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  omega

/-! ### The face sites are joined by the face bonds and the connector bonds -/

/-- The centre `σ R e_i` of the face `{x_i = σ R}` of `Q_R`. -/
def faceCentre (R : ℕ) (i : Fin d) (σ : ℤ) : Vertex d := Function.update 0 i (σ * R)

theorem faceCentre_self (R : ℕ) (i : Fin d) (σ : ℤ) : faceCentre R i σ i = σ * R :=
  Function.update_self _ _ _

theorem faceCentre_ne (R : ℕ) {i k : Fin d} (σ : ℤ) (hk : k ≠ i) : faceCentre R i σ k = 0 := by
  simp [faceCentre, hk]

/-- Inside one face, two face sites are joined along face bonds (a staircase between them). -/
theorem reachable_face {R : ℕ} {ω : Configuration d} (hface : ∀ e ∈ faceBonds d R, ω e = true)
    {a b : Vertex d} {i : Fin d} (hi : |a i| = R) (hbi : b i = a i)
    (ha : ∀ j, j ≠ i → |a j| < R) (hb : ∀ j, j ≠ i → |b j| < R) :
    (openGraph ω).Reachable a b := by
  obtain ⟨W, hW⟩ := stair_walk a b
  refine openGraph_reachable_of_walk hface W (fun e he => ?_)
  obtain ⟨f, hf, hfe⟩ := hW e he
  refine ⟨f, fun z hz => ⟨i, ?_, fun j hj => ?_⟩, hfe⟩
  · have h := stairBonds_box hf hz i
    rw [hbi] at h
    have : z i = a i := by simp only [min_self, max_self] at h; omega
    rw [this]; exact hi
  · have h := stairBonds_box hf hz j
    have h1 := abs_lt.mp (ha j hj)
    have h2 := abs_lt.mp (hb j hj)
    rw [abs_lt]
    constructor <;> omega

theorem reachable_centre {R : ℕ} {ω : Configuration d} (hR : 1 ≤ R)
    (hface : ∀ e ∈ faceBonds d R, ω e = true) {x : Vertex d} (hx : x ∈ faceSites d R) :
    ∃ (i : Fin d) (σ : ℤ), (σ = 1 ∨ σ = -1) ∧ (openGraph ω).Reachable x (faceCentre R i σ) := by
  obtain ⟨i, hi, hj⟩ := hx
  have key : ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → x i = σ * R →
      (openGraph ω).Reachable x (faceCentre R i σ) := by
    intro σ _ hσx
    refine reachable_face hface hi (by rw [faceCentre_self, hσx]) hj (fun k hk => ?_)
    rw [faceCentre_ne R σ hk]
    simp; omega
  rcases (abs_eq (Nat.cast_nonneg R)).mp hi with h | h
  · exact ⟨i, 1, Or.inl rfl, key 1 (Or.inl rfl) (by rw [h]; ring)⟩
  · exact ⟨i, -1, Or.inr rfl, key (-1) (Or.inr rfl) (by rw [h]; ring)⟩

theorem connector_adj_first {R : ℕ} {ω : Configuration d} (hconn : ∀ e ∈ connectorBonds d R, ω e = true)
    {i j : Fin d} {σ τ : ℤ} (hij : i ≠ j) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (openGraph ω).Adj (edgeSite R i j σ τ)
      (Function.update (edgeSite R i j σ τ) j (τ * ((R : ℤ) - 1))) := by
  have hadj : (nearestNeighborGraph d).Adj (edgeSite R i j σ τ)
      (Function.update (edgeSite R i j σ τ) j (τ * ((R : ℤ) - 1))) := by
    refine adj_update j ?_
    rw [edgeSite_other hij]
    rcases hτ with rfl | rfl
    · right; ring
    · left; ring
  exact ⟨hadj, hconn _ ⟨i, j, hij, σ, τ, hσ, hτ, Or.inl rfl⟩⟩

theorem connector_adj_second {R : ℕ} {ω : Configuration d} (hconn : ∀ e ∈ connectorBonds d R, ω e = true)
    {i j : Fin d} {σ τ : ℤ} (hij : i ≠ j) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (openGraph ω).Adj (edgeSite R i j σ τ)
      (Function.update (edgeSite R i j σ τ) i (σ * ((R : ℤ) - 1))) := by
  have hadj : (nearestNeighborGraph d).Adj (edgeSite R i j σ τ)
      (Function.update (edgeSite R i j σ τ) i (σ * ((R : ℤ) - 1))) := by
    refine adj_update i ?_
    rw [edgeSite_self]
    rcases hσ with rfl | rfl
    · right; ring
    · left; ring
  exact ⟨hadj, hconn _ ⟨i, j, hij, σ, τ, hσ, hτ, Or.inr rfl⟩⟩

theorem reachable_centres_ne {R : ℕ} {ω : Configuration d} (hR : 1 ≤ R)
    (hface : ∀ e ∈ faceBonds d R, ω e = true) (hconn : ∀ e ∈ connectorBonds d R, ω e = true)
    {i j : Fin d} {σ τ : ℤ} (hij : i ≠ j) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (openGraph ω).Reachable (faceCentre R i σ) (faceCentre R j τ) := by
  have h1 : (openGraph ω).Reachable (faceCentre R i σ)
      (Function.update (edgeSite R i j σ τ) j (τ * ((R : ℤ) - 1))) := by
    refine reachable_face hface (i := i) ?_ ?_ ?_ (update_first_props hR hij hσ hτ).2
    · rw [faceCentre_self, abs_sign_mul hσ]; simp
    · rw [Function.update_of_ne hij, edgeSite_self, faceCentre_self]
    · intro k hk
      rw [faceCentre_ne R σ hk]
      simp; omega
  have h2 : (openGraph ω).Reachable (Function.update (edgeSite R i j σ τ) i (σ * ((R : ℤ) - 1)))
      (faceCentre R j τ) := by
    refine reachable_face hface (i := j) (update_second_props hR hij hσ hτ).1 ?_
      (update_second_props hR hij hσ hτ).2 ?_
    · rw [Function.update_of_ne (Ne.symm hij), edgeSite_other hij, faceCentre_self]
    · intro k hk
      rw [faceCentre_ne R τ hk]
      simp; omega
  exact h1.trans ((connector_adj_first hconn hij hσ hτ).symm.reachable.trans
    ((connector_adj_second hconn hij hσ hτ).reachable.trans h2))

theorem reachable_centres (hd : 2 ≤ d) {R : ℕ} {ω : Configuration d} (hR : 1 ≤ R)
    (hface : ∀ e ∈ faceBonds d R, ω e = true) (hconn : ∀ e ∈ connectorBonds d R, ω e = true)
    {i j : Fin d} {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    (openGraph ω).Reachable (faceCentre R i σ) (faceCentre R j τ) := by
  by_cases hij : i = j
  · subst hij
    by_cases hστ : σ = τ
    · subst hστ; rfl
    · obtain ⟨k, hki⟩ := exists_other hd i
      exact (reachable_centres_ne hR hface hconn (Ne.symm hki) hσ (Or.inl rfl) :
        (openGraph ω).Reachable (faceCentre R i σ) (faceCentre R k 1)).trans
        (reachable_centres_ne hR hface hconn hki (Or.inl rfl) hτ)
  · exact reachable_centres_ne hR hface hconn hij hσ hτ

/-- G13 -/
theorem reachable_of_faceSites (hd : 2 ≤ d) {R : ℕ} (hR : 2 ≤ R) {ω : Configuration d}
    (hface : ∀ e ∈ faceBonds d R, ω e = true) (hconn : ∀ e ∈ connectorBonds d R, ω e = true)
    {x y : Vertex d} (hx : x ∈ faceSites d R) (hy : y ∈ faceSites d R) :
    (openGraph ω).Reachable x y := by
  obtain ⟨i, σ, hσ, hxc⟩ := reachable_centre (by omega) hface hx
  obtain ⟨j, τ, hτ, hyc⟩ := reachable_centre (by omega) hface hy
  exact hxc.trans ((reachable_centres hd (by omega) hface hconn hσ hτ).trans hyc.symm)

/-! ### The branch -/

/-- G14 -/
theorem refSite_mem_faceSites (hd : 2 ≤ d) {R : ℕ} (hR : 2 ≤ R) :
    refSite d R ∈ faceSites d R := by
  refine ⟨⟨1, by omega⟩, ?_, fun j hj => ?_⟩
  · rw [refSite, zeroPad_one hd]
    simp
  · have hj1 : j.val ≠ 1 := fun h => hj (Fin.ext h)
    simp only [refSite, zeroPad_apply, hj1, if_false]
    split_ifs
    · simp; omega
    · simp; omega

/-- G14 -/
theorem innerNeighbor_refSite {R : ℕ} (hR : 2 ≤ R) :
    innerNeighbor R (refSite d R) = zeroPad d (1, -((R : ℤ) - 1)) := by
  funext i
  by_cases h0 : i.val = 0
  · simp only [innerNeighbor, refSite, zeroPad_apply, h0, if_true]
    rw [if_neg (by simp; omega)]
  · by_cases h1 : i.val = 1
    · simp only [innerNeighbor, refSite, zeroPad_apply, h1, one_ne_zero, if_true, if_false]
      rw [if_pos (by simp), Int.sign_eq_neg_one_of_neg (by omega)]
      ring
    · simp [innerNeighbor, refSite, zeroPad_apply, h0, h1]

/-- G15 -/
theorem gadget_mem_cube_pred (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {g : Vertex d}
    (hg : g ∈ ambientSites hd (R : ℤ)) : gadgetShift d R + g ∈ cube d (R - 1) := by
  obtain ⟨hg01, hg2⟩ := hg
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hd0 : 0 < d := by omega
  have hd1 : 1 < d := by omega
  intro i
  simp only [Pi.add_apply, gadgetShift, zeroPad]
  rw [abs_le]
  by_cases h0 : i.val = 0
  · obtain rfl : i = ⟨0, hd0⟩ := Fin.ext h0
    simp only [if_true]
    constructor <;> omega
  · by_cases h1 : i.val = 1
    · obtain rfl : i = ⟨1, hd1⟩ := Fin.ext h1
      simp only [if_true, one_ne_zero, if_false]
      constructor <;> omega
    · rw [if_neg h0, if_neg h1, hg2 i (by omega)]
      constructor <;> omega

/-- G16 -/
theorem highBranch_sites (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) :
    ∀ z ∈ bondSites (chainBonds (highWaypoints d R)), z ∈ cube d (R - 1) ∧
      ∃ v : ℤ, -((R : ℤ) - 1) ≤ v ∧ v ≤ -halfSide R - 1 ∧ z = zeroPad d (1, v) := by
  rintro z ⟨e, he, hz⟩
  simp only [highWaypoints, chainBonds, Set.union_empty] at he
  have hz' := stairBonds_box he hz
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hd1 : 1 < d := by omega
  have h1 := hz' ⟨1, hd1⟩
  simp only [zeroPad_one hd] at h1
  have hex : ∃ v : ℤ, -((R : ℤ) - 1) ≤ v ∧ v ≤ -halfSide R - 1 ∧ z = zeroPad d (1, v) := by
    refine ⟨z ⟨1, hd1⟩, by omega, by omega, ?_⟩
    funext i
    have := hz' i
    simp only [zeroPad_apply] at this ⊢
    by_cases h0 : i.val = 0
    · simp only [h0, if_true] at this ⊢; omega
    · by_cases h1 : i.val = 1
      · obtain rfl : i = ⟨1, hd1⟩ := Fin.ext h1
        simp
      · simp only [h0, h1, if_false] at this ⊢; omega
  obtain ⟨v, hv1, hv2, rfl⟩ := hex
  refine ⟨zeroPad_mem_cube ?_ ?_, v, hv1, hv2, rfl⟩
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

/-- G19 -/
theorem zeroPad_s_mem (hd : 2 ≤ d) (R : ℕ) :
    zeroPad d (-2, -halfSide R - 1) - gadgetShift d R ∈ ambientSites hd (R : ℤ) := by
  rw [zeroPad_terminal_s, add_sub_cancel_left]
  exact zeroPad_one_one_mem hd R

/-- G19 -/
theorem zeroPad_t_mem (hd : 2 ≤ d) (R : ℕ) :
    zeroPad d (1, -halfSide R - 1) - gadgetShift d R ∈ ambientSites hd (R : ℤ) := by
  rw [zeroPad_terminal_t, add_sub_cancel_left]
  exact zeroPad_four_one_mem hd R

/-- The two ends of a polygonal path with distinct ends are sites of the path. -/
theorem ends_mem_bondSites_chain {l : List (Vertex d)} {a b : Vertex d} (ha : l.head? = some a)
    (hb : l.getLast? = some b) (hab : a ≠ b) :
    a ∈ bondSites (chainBonds l) ∧ b ∈ bondSites (chainBonds l) := by
  cases l with
  | nil => simp at ha
  | cons a' l' =>
    obtain rfl : a' = a := by simpa using ha
    obtain ⟨W, hW⟩ := chain_walk a' l'
    have hlast : (a' :: l').getLast (List.cons_ne_nil _ _) = b := by
      rw [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _)] at hb
      exact Option.some.inj hb
    have key : ∀ (u v : Vertex d) (W : (nearestNeighborGraph d).Walk u v), u ≠ v →
        (∀ e ∈ W.edges, ∃ f ∈ chainBonds (a' :: l'), (f : Sym2 (Vertex d)) = e) →
        u ∈ bondSites (chainBonds (a' :: l')) := by
      intro u v W huv hW
      cases W with
      | nil => exact absurd rfl huv
      | @cons _ w' _ h W' =>
        obtain ⟨f, hf, hfe⟩ := hW s(u, w') (by simp)
        exact ⟨f, hf, by rw [hfe]; simp⟩
    have hW' : ∀ e ∈ (W.copy rfl hlast).edges,
        ∃ f ∈ chainBonds (a' :: l'), (f : Sym2 (Vertex d)) = e := by
      intro e he
      rw [SimpleGraph.Walk.edges_copy] at he
      exact hW e he
    refine ⟨key a' b (W.copy rfl hlast) hab hW', key b a' (W.copy rfl hlast).reverse hab.symm ?_⟩
    intro e he
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact hW' e he

/-! ### The branch `P₁` -/

/-- `z` lies on the shell `∂Q_{R-1}` and is not the site `(1, -(R-1))`. -/
abbrev ShellSite (d R : ℕ) (z : Vertex d) : Prop :=
  (∃ k, |z k| = (R : ℤ) - 1) ∧ z ≠ zeroPad d (1, -((R : ℤ) - 1))

/-- A site of `P₁`: on the shell and different from `(1, -(R-1))`, or on the column `x_0 = -2`. -/
abbrev LowSite (d R : ℕ) (z : Vertex d) : Prop :=
  z ∈ cube d (R - 1) ∧ (ShellSite d R z ∨
    ∃ v : ℤ, -((R : ℤ) - 1) ≤ v ∧ v ≤ -halfSide R - 1 ∧ z = zeroPad d (-2, v))

theorem bondSites_stair_box {a b z : Vertex d} (hz : z ∈ bondSites (stairBonds a b)) (i : Fin d) :
    min (a i) (b i) ≤ z i ∧ z i ≤ max (a i) (b i) := by
  obtain ⟨e, he, hze⟩ := hz
  exact stairBonds_box he hze i

theorem stair_update_box {a z : Vertex d} {j : Fin d} {v : ℤ}
    (hz : z ∈ bondSites (stairBonds a (Function.update a j v))) :
    (∀ i, i ≠ j → z i = a i) ∧ min (a j) v ≤ z j ∧ z j ≤ max (a j) v := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have h := bondSites_stair_box hz i
    rw [Function.update_of_ne hi] at h
    simp only [min_self, max_self] at h
    omega
  · have h := bondSites_stair_box hz j
    rwa [Function.update_self] at h

theorem fin_zero_ne_one (hd : 2 ≤ d) : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
  simp [Fin.ext_iff]

theorem leg_two (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {p z : Vertex d} (hp : p ∈ cube d (R - 1))
    (hP : ∃ k, |p k| = (R : ℤ) - 1 ∧ (k ≠ ⟨1, by omega⟩ ∨ p ⟨1, by omega⟩ = (R : ℤ) - 1))
    (hpa : p ≠ zeroPad d (1, -((R : ℤ) - 1)))
    (hz : z ∈ bondSites (stairBonds p (Function.update p ⟨1, by omega⟩ ((R : ℤ) - 1)))) :
    ShellSite d R z := by
  obtain ⟨hz1, hz2, hz3⟩ := stair_update_box hz
  obtain ⟨k, hk, hk'⟩ := hP
  have hp1 := abs_le.mp (hp ⟨1, by omega⟩)
  refine ⟨?_, ?_⟩
  · rcases hk' with hne | h1
    · exact ⟨k, by rw [hz1 k hne]; exact hk⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rw [abs_eq (by omega)]
      left; omega
  · intro hza
    apply hpa
    funext i
    by_cases hi : i = ⟨1, by omega⟩
    · subst hi
      have := congrFun hza ⟨1, by omega⟩
      rw [zeroPad_one hd] at this ⊢
      omega
    · exact (hz1 i hi).symm.trans (congrFun hza i)

theorem leg_three (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {q z : Vertex d} {v : ℤ}
    (hq : q ⟨1, by omega⟩ = (R : ℤ) - 1)
    (hz : z ∈ bondSites (stairBonds q (Function.update q ⟨0, by omega⟩ v))) :
    ShellSite d R z := by
  obtain ⟨hz1, -, -⟩ := stair_update_box hz
  have h1 : z ⟨1, by omega⟩ = (R : ℤ) - 1 := by
    rw [hz1 _ (fin_zero_ne_one hd).symm, hq]
  refine ⟨⟨⟨1, by omega⟩, by rw [h1]; exact abs_of_nonneg (by omega)⟩, fun hza => ?_⟩
  have := congrFun hza ⟨1, by omega⟩
  rw [zeroPad_one hd, h1] at this
  omega

theorem leg_four (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {q z : Vertex d} {v : ℤ}
    (hq : q ⟨0, by omega⟩ = -((R : ℤ) - 1))
    (hz : z ∈ bondSites (stairBonds q (Function.update q ⟨1, by omega⟩ v))) :
    ShellSite d R z := by
  obtain ⟨hz1, -, -⟩ := stair_update_box hz
  have h1 : z ⟨0, by omega⟩ = -((R : ℤ) - 1) := by
    rw [hz1 _ (fin_zero_ne_one hd), hq]
  refine ⟨⟨⟨0, by omega⟩, by rw [h1, abs_neg]; exact abs_of_nonneg (by omega)⟩, fun hza => ?_⟩
  have := congrFun hza ⟨0, by omega⟩
  rw [zeroPad_zero hd, h1] at this
  omega

theorem leg_five (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {q z : Vertex d}
    (hq : q ⟨0, by omega⟩ = -((R : ℤ) - 1))
    (hz : z ∈ bondSites (stairBonds q (zeroPad d (-((R : ℤ) - 1), -((R : ℤ) - 1))))) :
    ShellSite d R z := by
  have hb := bondSites_stair_box hz ⟨0, by omega⟩
  rw [zeroPad_zero hd, hq] at hb
  have h1 : z ⟨0, by omega⟩ = -((R : ℤ) - 1) := by simp only [min_self, max_self] at hb; omega
  refine ⟨⟨⟨0, by omega⟩, by rw [h1, abs_neg]; exact abs_of_nonneg (by omega)⟩, fun hza => ?_⟩
  have := congrFun hza ⟨0, by omega⟩
  rw [zeroPad_zero hd, h1] at this
  omega

theorem leg_six (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {z : Vertex d}
    (hz : z ∈ bondSites (stairBonds (zeroPad d (-((R : ℤ) - 1), -((R : ℤ) - 1)))
      (zeroPad d (-2, -((R : ℤ) - 1))))) : ShellSite d R z := by
  have hb := bondSites_stair_box hz ⟨1, by omega⟩
  have hb0 := bondSites_stair_box hz ⟨0, by omega⟩
  rw [zeroPad_one hd, zeroPad_one hd] at hb
  rw [zeroPad_zero hd, zeroPad_zero hd] at hb0
  have h1 : z ⟨1, by omega⟩ = -((R : ℤ) - 1) := by simp only [min_self, max_self] at hb; omega
  refine ⟨⟨⟨1, by omega⟩, by rw [h1, abs_neg]; exact abs_of_nonneg (by omega)⟩, fun hza => ?_⟩
  have := congrFun hza ⟨0, by omega⟩
  rw [zeroPad_zero hd] at this
  omega

theorem stair_zeroPad_col (hd : 2 ≤ d) {c u u' : ℤ} {z : Vertex d}
    (hz : z ∈ bondSites (stairBonds (zeroPad d (c, u)) (zeroPad d (c, u')))) :
    z = zeroPad d (c, z ⟨1, by omega⟩) ∧ min u u' ≤ z ⟨1, by omega⟩ ∧
      z ⟨1, by omega⟩ ≤ max u u' := by
  have hd1 : 1 < d := by omega
  have h1 := bondSites_stair_box hz ⟨1, hd1⟩
  simp only [zeroPad_one hd] at h1
  refine ⟨?_, h1⟩
  funext i
  have := bondSites_stair_box hz i
  simp only [zeroPad_apply] at this ⊢
  by_cases h0 : i.val = 0
  · simp only [h0, if_true] at this ⊢; simp only [min_self, max_self] at this; omega
  · by_cases h1 : i.val = 1
    · obtain rfl : i = ⟨1, hd1⟩ := Fin.ext h1
      simp
    · simp only [h0, h1, if_false] at this ⊢; simp only [min_self, max_self] at this; omega

theorem leg_seven (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {z : Vertex d}
    (hz : z ∈ bondSites (stairBonds (zeroPad d (-2, -((R : ℤ) - 1)))
      (zeroPad d (-2, -halfSide R - 1)))) :
    ∃ v : ℤ, -((R : ℤ) - 1) ≤ v ∧ v ≤ -halfSide R - 1 ∧ z = zeroPad d (-2, v) := by
  obtain ⟨h1, h2, h3⟩ := stair_zeroPad_col hd hz
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  exact ⟨_, by omega, by omega, h1⟩

theorem lowChain_sites (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {w1 p₀ p₁ p₂ p₃ : Vertex d}
    (hw1 : w1 ∈ cube d (R - 1)) (hp0 : p₀ ∈ cube d (R - 1))
    (hp1 : p₁ = Function.update p₀ ⟨1, by omega⟩ ((R : ℤ) - 1))
    (hp2 : p₂ = Function.update p₁ ⟨0, by omega⟩ (-((R : ℤ) - 1)))
    (hp3 : p₃ = Function.update p₂ ⟨1, by omega⟩ (-((R : ℤ) - 1)))
    (hL1 : ∀ z ∈ bondSites (stairBonds w1 p₀), ShellSite d R z)
    (hP : ∃ k, |p₀ k| = (R : ℤ) - 1 ∧ (k ≠ ⟨1, by omega⟩ ∨ p₀ ⟨1, by omega⟩ = (R : ℤ) - 1))
    (hpa : p₀ ≠ zeroPad d (1, -((R : ℤ) - 1))) :
    ∀ z ∈ bondSites (chainBonds [w1, p₀, p₁, p₂, p₃,
      zeroPad d (-((R : ℤ) - 1), -((R : ℤ) - 1)), zeroPad d (-2, -((R : ℤ) - 1)),
      zeroPad d (-2, -halfSide R - 1)]), LowSite d R z := by
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hcube1 : p₁ ∈ cube d (R - 1) := by
    rw [hp1]; exact update_mem_cube hp0 _ (by rw [abs_le]; constructor <;> omega)
  have hcube2 : p₂ ∈ cube d (R - 1) := by
    rw [hp2]; exact update_mem_cube hcube1 _ (by rw [abs_le]; constructor <;> omega)
  have hcube3 : p₃ ∈ cube d (R - 1) := by
    rw [hp3]; exact update_mem_cube hcube2 _ (by rw [abs_le]; constructor <;> omega)
  have hall : ∀ a ∈ [w1, p₀, p₁, p₂, p₃,
      zeroPad d (-((R : ℤ) - 1), -((R : ℤ) - 1)), zeroPad d (-2, -((R : ℤ) - 1)),
      zeroPad d (-2, -halfSide R - 1)], a ∈ cube d (R - 1) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hw1
    · exact hp0
    · exact hcube1
    · exact hcube2
    · exact hcube3
    · exact zeroPad_mem_cube (by rw [abs_le]; constructor <;> omega)
        (by rw [abs_le]; constructor <;> omega)
    · exact zeroPad_mem_cube (by rw [abs_le]; constructor <;> omega)
        (by rw [abs_le]; constructor <;> omega)
    · exact zeroPad_mem_cube (by rw [abs_le]; constructor <;> omega)
        (by rw [abs_le]; constructor <;> omega)
  rintro z ⟨e, he, hze⟩
  have hzc : z ∈ cube d (R - 1) := chainBonds_cube hall e he z hze
  refine ⟨hzc, ?_⟩
  simp only [chainBonds, Set.mem_union, Set.mem_empty_iff_false, or_false] at he
  rcases he with he | he | he | he | he | he | he
  · exact Or.inl (hL1 z ⟨e, he, hze⟩)
  · rw [hp1] at he
    exact Or.inl (leg_two hd hR hp0 hP hpa ⟨e, he, hze⟩)
  · refine Or.inl (leg_three hd hR (q := p₁) ?_ ⟨e, by rw [hp2] at he; exact he, hze⟩)
    rw [hp1, Function.update_self]
  · refine Or.inl (leg_four hd hR (q := p₂) ?_ ⟨e, by rw [hp3] at he; exact he, hze⟩)
    rw [hp2, Function.update_self]
  · refine Or.inl (leg_five hd hR (q := p₃) ?_ ⟨e, he, hze⟩)
    rw [hp3, Function.update_of_ne (fin_zero_ne_one hd), hp2, Function.update_self]
  · exact Or.inl (leg_six hd hR ⟨e, he, hze⟩)
  · exact Or.inr (leg_seven hd hR ⟨e, he, hze⟩)

theorem abs_innerNeighbor_face {R : ℕ} (hR : 1 ≤ R) {x : Vertex d} {i : Fin d} (hi : |x i| = R) :
    |innerNeighbor R x i| = (R : ℤ) - 1 := by
  rw [innerNeighbor_apply_self hi, abs_eq (by omega)]
  rcases sign_sub_of_abs hR hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem innerNeighbor_ne_ref (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {w : Vertex d}
    (hw : w ∈ faceSites d R) (hpre : w ⟨1, by omega⟩ ≠ -(R : ℤ)) :
    innerNeighbor R w ≠ zeroPad d (1, -((R : ℤ) - 1)) := by
  have hd1 : 1 < d := by omega
  obtain ⟨i, hi, hj⟩ := hw
  intro h
  have h1 := abs_innerNeighbor_face (by omega) hi
  have h2 := congrFun h i
  by_cases h0 : i.val = 0
  · rw [h2] at h1
    simp only [zeroPad_apply, h0, if_true] at h1
    simp at h1; omega
  · by_cases hi1 : i.val = 1
    · obtain rfl : i = ⟨1, hd1⟩ := Fin.ext hi1
      rw [innerNeighbor_apply_self hi, zeroPad_one hd] at h2
      rcases sign_sub_of_abs (by omega) hi with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    · rw [h2] at h1
      simp only [zeroPad_apply, h0, hi1, if_false] at h1
      simp at h1; omega

theorem preWaypoint_props (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {w : Vertex d}
    (hw : w ∈ faceSites d R) (hw0 : w ≠ refSite d R) :
    preWaypoint hd R w ∈ cube d (R - 1) ∧
    (∀ z ∈ bondSites (stairBonds (innerNeighbor R w) (preWaypoint hd R w)), ShellSite d R z) ∧
    (∃ k, |preWaypoint hd R w k| = (R : ℤ) - 1 ∧
      (k ≠ ⟨1, by omega⟩ ∨ preWaypoint hd R w ⟨1, by omega⟩ = (R : ℤ) - 1)) ∧
    preWaypoint hd R w ≠ zeroPad d (1, -((R : ℤ) - 1)) := by
  have hd0 : 0 < d := by omega
  have hd1 : 1 < d := by omega
  have hw1c := innerNeighbor_mem_cube (by omega) hw
  by_cases hpre : w ⟨1, hd1⟩ = -(R : ℤ)
  · obtain ⟨i, hi, hj⟩ := hw
    have hi1 : i = ⟨1, hd1⟩ := by
      by_contra h
      have := hj ⟨1, hd1⟩ (Ne.symm h)
      rw [hpre, abs_neg] at this
      simp at this
    subst hi1
    have hw1_1 : innerNeighbor R w ⟨1, hd1⟩ = -((R : ℤ) - 1) := by
      rw [innerNeighbor_apply_self hi]
      rcases sign_sub_of_abs (by omega) hi with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have hw1_ne : ∀ k, k ≠ ⟨1, hd1⟩ → innerNeighbor R w k = w k :=
      fun k hk => innerNeighbor_apply_ne hj hk
    obtain ⟨v, hvc, hpw⟩ : ∃ v : ℤ, ((1 ≤ w ⟨0, hd0⟩ ∧ v = (R : ℤ) - 1) ∨
        (w ⟨0, hd0⟩ < 1 ∧ v = -((R : ℤ) - 1))) ∧
        preWaypoint hd R w = Function.update (innerNeighbor R w) ⟨0, hd0⟩ v := by
      by_cases h : 1 ≤ w ⟨0, hd0⟩
      · refine ⟨(R : ℤ) - 1, Or.inl ⟨h, rfl⟩, ?_⟩
        unfold preWaypoint; rw [if_pos hpre, if_pos h]
      · refine ⟨-((R : ℤ) - 1), Or.inr ⟨by omega, rfl⟩, ?_⟩
        unfold preWaypoint; rw [if_pos hpre, if_neg h]
    rw [hpw]
    refine ⟨update_mem_cube hw1c _ (by rw [abs_le]; omega), ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := stair_update_box hz
      refine ⟨⟨⟨1, hd1⟩, ?_⟩, fun hza => hw0 ?_⟩
      · rw [hz1 _ (fin_zero_ne_one hd).symm, hw1_1, abs_neg, abs_of_nonneg (by omega)]
      · funext k
        by_cases hk0 : k = ⟨0, hd0⟩
        · subst hk0
          have h0 := congrFun hza ⟨0, hd0⟩
          rw [zeroPad_zero hd] at h0
          rw [refSite, zeroPad_zero hd]
          have := hw1_ne ⟨0, hd0⟩ (fin_zero_ne_one hd)
          omega
        · by_cases hk1 : k = ⟨1, hd1⟩
          · subst hk1; rw [refSite, zeroPad_one hd]; exact hpre
          · have hk2 : 2 ≤ k.val := by
              have : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
              have : k.val ≠ 1 := fun h => hk1 (Fin.ext h)
              omega
            rw [refSite, zeroPad_extra _ k hk2]
            have h2 := congrFun hza k
            rw [zeroPad_extra _ k hk2] at h2
            rw [← hw1_ne k hk1, ← hz1 k hk0, h2]
    · refine ⟨⟨0, hd0⟩, ?_, Or.inl (fin_zero_ne_one hd)⟩
      rw [Function.update_self, abs_eq (by omega)]
      omega
    · intro h
      have := congrFun h ⟨0, hd0⟩
      rw [Function.update_self, zeroPad_zero hd] at this
      omega
  · have hpw : preWaypoint hd R w = innerNeighbor R w := by
      unfold preWaypoint; rw [if_neg hpre]
    rw [hpw]
    have hne := innerNeighbor_ne_ref hd hR hw hpre
    obtain ⟨i, hi, hj⟩ := hw
    refine ⟨hw1c, ?_, ?_, hne⟩
    · intro z hz
      have hzw : z = innerNeighbor R w := by
        funext k
        have := bondSites_stair_box hz k
        simp only [min_self, max_self] at this
        omega
      rw [hzw]
      exact ⟨⟨i, abs_innerNeighbor_face (by omega) hi⟩, hne⟩
    · refine ⟨i, abs_innerNeighbor_face (by omega) hi, ?_⟩
      by_cases hi1 : i = ⟨1, hd1⟩
      · right
        subst hi1
        rw [innerNeighbor_apply_self hi]
        rcases sign_sub_of_abs (by omega) hi with ⟨a, b⟩ | ⟨a, b⟩
        · omega
        · exact absurd a hpre
      · left; exact hi1

theorem lowSite_spec (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {z : Vertex d} (hz : LowSite d R z) :
    z ∈ cube d (R - 1) ∧ z ∉ bondSites (chainBonds (highWaypoints d R)) ∧
      (z - gadgetShift d R ∈ ambientSites hd (R : ℤ) → z = zeroPad d (-2, -halfSide R - 1)) := by
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hd0 : 0 < d := by omega
  have hd1 : 1 < d := by omega
  obtain ⟨hzc, hz'⟩ := hz
  refine ⟨hzc, ?_, ?_⟩
  · intro hzH
    obtain ⟨-, v, hv1, hv2, hzv⟩ := highBranch_sites hd hR z hzH
    rcases hz' with ⟨⟨k, hk⟩, hza⟩ | ⟨v', hv'1, hv'2, hzv'⟩
    · apply hza
      rw [hzv] at hk ⊢
      by_cases h0 : k.val = 0
      · simp only [zeroPad_apply, h0, if_true] at hk
        simp at hk; omega
      · by_cases h1 : k.val = 1
        · simp only [zeroPad_apply, h1, one_ne_zero, if_true, if_false] at hk
          rw [abs_eq (by omega)] at hk
          have : v = -((R : ℤ) - 1) := by omega
          rw [this]
        · simp only [zeroPad_apply, h0, h1, if_false] at hk
          simp at hk; omega
    · rw [hzv] at hzv'
      have h := congrArg Prod.fst (zeroPad_injective hd hzv')
      norm_num at h
  · intro hg
    obtain ⟨hg01, hg2⟩ := hg
    rcases hz' with ⟨⟨k, hk⟩, -⟩ | ⟨v, hv1, hv2, rfl⟩
    · exfalso
      simp only [Pi.sub_apply, gadgetShift, zeroPad_zero hd, zeroPad_one hd] at hg01
      by_cases h0 : k = ⟨0, hd0⟩
      · subst h0
        rw [abs_eq (by omega)] at hk
        omega
      · by_cases h1 : k = ⟨1, hd1⟩
        · subst h1
          rw [abs_eq (by omega)] at hk
          omega
        · have hk2 : 2 ≤ k.val := by
            have : k.val ≠ 0 := fun h => h0 (Fin.ext h)
            have : k.val ≠ 1 := fun h => h1 (Fin.ext h)
            omega
          have := hg2 k hk2
          simp only [Pi.sub_apply, gadgetShift, zeroPad_extra _ k hk2, sub_zero] at this
          rw [this] at hk
          simp at hk; omega
    · simp only [Pi.sub_apply, gadgetShift, zeroPad_zero hd, zeroPad_one hd] at hg01
      have : v = -halfSide R - 1 := by omega
      rw [this]

/-- G17 -/
theorem lowBranch_sites (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {w : Vertex d}
    (hw : w ∈ faceSites d R) (hw0 : w ≠ refSite d R) :
    ∀ z ∈ bondSites (chainBonds (lowWaypoints hd R w)), z ∈ cube d (R - 1) ∧
      z ∉ bondSites (chainBonds (highWaypoints d R)) ∧
      (z - gadgetShift d R ∈ ambientSites hd (R : ℤ) → z = zeroPad d (-2, -halfSide R - 1)) := by
  intro z hz
  obtain ⟨hp0, hL1, hP, hpa⟩ := preWaypoint_props hd hR hw hw0
  have hw1c := innerNeighbor_mem_cube (by omega) hw
  simp only [lowWaypoints] at hz
  exact lowSite_spec hd hR (lowChain_sites hd hR hw1c hp0 rfl rfl rfl hL1 hP hpa z hz)

/-- G18 -/
theorem lowBranch_ends (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) {w : Vertex d}
    (hw : w ∈ faceSites d R) :
    innerNeighbor R w ∈ bondSites (chainBonds (lowWaypoints hd R w)) ∧
      zeroPad d (-2, -halfSide R - 1) ∈ bondSites (chainBonds (lowWaypoints hd R w)) := by
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hne : innerNeighbor R w ≠ zeroPad d (-2, -halfSide R - 1) := by
    obtain ⟨i, hi, hj⟩ := hw
    intro h
    have h1 := abs_innerNeighbor_face (by omega) hi
    rw [congrFun h i] at h1
    by_cases h0 : i.val = 0
    · simp only [zeroPad_apply, h0, if_true] at h1
      simp at h1; omega
    · by_cases h1' : i.val = 1
      · simp only [zeroPad_apply, h1', one_ne_zero, if_true, if_false] at h1
        rw [abs_eq (by omega)] at h1
        omega
      · simp only [zeroPad_apply, h0, h1', if_false] at h1
        simp at h1; omega
  exact ends_mem_bondSites_chain (l := lowWaypoints hd R w) rfl rfl hne

/-- G18 -/
theorem highBranch_ends (hd : 2 ≤ d) {R : ℕ} (hR : 10 ≤ R) :
    zeroPad d (1, -((R : ℤ) - 1)) ∈ bondSites (chainBonds (highWaypoints d R)) ∧
      zeroPad d (1, -halfSide R - 1) ∈ bondSites (chainBonds (highWaypoints d R)) := by
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hne : zeroPad d (1, -((R : ℤ) - 1)) ≠ zeroPad d (1, -halfSide R - 1) := by
    intro h
    have := congrArg Prod.snd (zeroPad_injective hd h)
    simp only at this
    omega
  exact ends_mem_bondSites_chain (l := highWaypoints d R) rfl rfl hne

end Rigidity.Proofs.S4.OuterNonConstant
