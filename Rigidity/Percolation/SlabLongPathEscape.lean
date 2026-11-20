import Rigidity.Percolation.SlabTransverseCrossing
import Rigidity.Percolation.SelectedPathSegment

/-!
# Paths escaping past a crossing component

A path separated from a cube-crossing component, with one vertex in an early
prefix and one beyond a later prefix, gives two disconnected components that
escape through the same sequence of slabs.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- A crossing component and a disconnected path spanning two prefixes yield
two disconnected roots that both escape the later prefix. -/
theorem IntegerCube.two_escapes_of_disconnected_path {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {width k₀ N : ℕ} (hstart : 0 < k₀ * width)
    (hend : (k₀ + N) * width < Q.size) {ω : Configuration d}
    {root : Vertex d}
    (hroot : IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
      (fun i => ↑(Q.upperFace i)) root)
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    {n : ℕ} {γ : Fin (n + 1) → Vertex d} (hγ : IsSelectedOpenPath ω Q.vertices large n γ)
    {a b : Fin (n + 1)} (ha : γ a ∈ Q.slabPrefix j width k₀)
    (hb : γ b ∉ Q.slabPrefix j width (k₀ + N))
    (hsep : ¬ (openIn ω Q.vertices).Reachable root (γ 0)) :
    ∃ z ∈ Q.slabPrefix j width k₀, ∃ z' ∈ Q.slabPrefix j width k₀,
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z ω ∧
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z' ω ∧
      ¬ (openIn ω Q.vertices).Reachable z z' := by
  obtain ⟨hL, hR⟩ := Q.faces_separated_by_prefixes j hstart hend
  obtain ⟨⟨u, huQ, huL, hru⟩, ⟨v, hvQ, hvR, hrv⟩⟩ := hroot.2 j
  refine ⟨u, hL huL, γ a, ha,
    ⟨v, hvQ, hR hvR, hru.symm.trans hrv⟩,
    ⟨γ b, hγ.mem_region b, ⟨hγ.mem_region b, hb⟩,
      (hγ.reachable_start a).symm.trans (hγ.reachable_start b)⟩, ?_⟩
  intro hconn
  exact hsep (hru.trans (hconn.trans (hγ.reachable_start a).symm))

open Classical in
/-- The probability of a path spanning two prefixes while disconnected from a
crossing component is bounded by the two-component slab survival estimate. -/
theorem IntegerCube.measureReal_disconnected_path_spanning_prefixes_le {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hstart : 0 < k₀ * width) (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (p : unitInterval) (ρ : ℝ) (hρ : ρ ≤ 1)
    (hprob : ∀ n < N, ∀ x ∈ Q.slab j width (k₀ + n),
      ∀ y ∈ Q.slab j width (k₀ + n), ρ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width (k₀ + n))).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ∃ root,
      IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) root ∧
      ∃ n γ, IsSelectedOpenPath ω Q.vertices large n γ ∧
        (∃ a, γ a ∈ Q.slabPrefix j width k₀) ∧
        (∃ b, γ b ∉ Q.slabPrefix j width (k₀ + N)) ∧
        ¬ (openIn ω Q.vertices).Reachable root (γ 0)} ≤
      ((Q.vertices.filter fun x => x ∈ Q.slabPrefix j width k₀).card : ℝ) ^ 2 *
        (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N := by
  classical
  let A := Q.vertices.filter fun x => x ∈ Q.slabPrefix j width k₀
  have hA : (↑A : Set (Vertex d)) ⊆ Q.slabPrefix j width k₀ := fun x hx =>
    (Finset.mem_filter.mp hx).2
  have hcover : {ω | ∃ root,
      IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) root ∧
      ∃ n γ, IsSelectedOpenPath ω Q.vertices large n γ ∧
        (∃ a, γ a ∈ Q.slabPrefix j width k₀) ∧
        (∃ b, γ b ∉ Q.slabPrefix j width (k₀ + N)) ∧
        ¬ (openIn ω Q.vertices).Reachable root (γ 0)} ⊆ {ω | ∃ z ∈ A, ∃ z' ∈ A,
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z ω ∧
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z' ω ∧
      ¬ (openIn ω Q.vertices).Reachable z z'} := by
    rintro ω ⟨root, hroot, n, γ, hγ, ⟨a, ha⟩, ⟨b, hb⟩, hsep⟩
    obtain ⟨z, hz, z', hz', h₁, h₂, h₃⟩ :=
      Q.two_escapes_of_disconnected_path j hstart (hsize N le_rfl) hroot hγ ha hb hsep
    exact ⟨z, Finset.mem_filter.mpr ⟨hz.1, hz⟩, z',
      Finset.mem_filter.mpr ⟨hz'.1, hz'⟩, h₁, h₂, h₃⟩
  apply (measureReal_mono hcover (measure_ne_top _ _)).trans
  exact Q.measureReal_exists_two_escapes_le j width k₀ N hwidth hsize A hA p ρ hρ hprob

/-- Vertices separated by `N + 1` slab widths span `N` consecutive slabs,
starting at the first slab boundary beyond the lower vertex. -/
theorem IntegerCube.exists_prefixes_between_vertices {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width N : ℕ) (hwidth : 0 < width) {x y : Vertex d}
    (hx : x ∈ Q.vertices) (hy : y ∈ Q.vertices)
    (hgap : ((N + 1) * width : ℕ) ≤ y j - x j) :
    ∃ k₀, 0 < k₀ * width ∧ (k₀ + N) * width < Q.size ∧
      x ∈ Q.slabPrefix j width k₀ ∧ y ∉ Q.slabPrefix j width (k₀ + N) := by
  let a : ℕ := (x j - Q.corner j).toNat
  let k₀ : ℕ := a / width + 1
  have hxj := (Q.mem_vertices x).mp hx j
  have hyj := (Q.mem_vertices y).mp hy j
  have ha : (a : ℤ) = x j - Q.corner j := by
    exact Int.toNat_of_nonneg (by omega)
  have hdiv := Nat.mod_add_div a width
  have hmod : a % width < width := Nat.mod_lt _ hwidth
  have hklo : a < k₀ * width := by
    dsimp only [k₀]
    nlinarith
  have hkhi : k₀ * width ≤ a + width := by
    dsimp only [k₀]
    nlinarith [Nat.zero_le (a % width)]
  have hkpos : 0 < k₀ * width := lt_of_le_of_lt (Nat.zero_le a) hklo
  have hbound : (k₀ + N) * width ≤ a + (N + 1) * width := by nlinarith
  have hbound' : (((k₀ + N) * width : ℕ) : ℤ) ≤
      (a : ℤ) + (((N + 1) * width : ℕ) : ℤ) := by exact_mod_cast hbound
  have hklo' : (a : ℤ) < ((k₀ * width : ℕ) : ℤ) := by exact_mod_cast hklo
  have hlast : (((k₀ + N) * width : ℕ) : ℤ) < Q.size := by omega
  have hsize : (k₀ + N) * width < Q.size := by exact_mod_cast hlast
  refine ⟨k₀, hkpos, hsize, ⟨hx, ?_⟩, ?_⟩
  · omega
  · intro hyP
    have hyP' := hyP.2
    omega

/-- Every path with sufficiently large coordinate diameter spans a sequence of
`N` slabs in one coordinate direction. -/
theorem IntegerCube.exists_prefixes_spanned_by_path {d : ℕ} (Q : IntegerCube d)
    (width N : ℕ) (hwidth : 0 < width) {ω : Configuration d}
    {n : ℕ} {γ : Fin (n + 1) → Vertex d}
    (hγ : IsSelectedOpenPath ω Q.vertices
      (pathDiameterAtLeast (((N + 1) * width : ℕ) : ℤ)) n γ) :
    ∃ j k₀, 0 < k₀ * width ∧ (k₀ + N) * width < Q.size ∧
      (∃ a, γ a ∈ Q.slabPrefix j width k₀) ∧
      ∃ b, γ b ∉ Q.slabPrefix j width (k₀ + N) := by
  obtain ⟨a, b, j, hdiam⟩ := hγ.1
  by_cases hab : γ a j ≤ γ b j
  · have hgap : (((N + 1) * width : ℕ) : ℤ) ≤ γ b j - γ a j := by
      rw [abs_of_nonpos (sub_nonpos.mpr hab)] at hdiam
      omega
    obtain ⟨k₀, hkpos, hksize, ha, hb⟩ :=
      Q.exists_prefixes_between_vertices j width N hwidth (hγ.mem_region a) (hγ.mem_region b) hgap
    exact ⟨j, k₀, hkpos, hksize, ⟨a, ha⟩, ⟨b, hb⟩⟩
  · have hba : γ b j ≤ γ a j := le_of_not_ge hab
    have hgap : (((N + 1) * width : ℕ) : ℤ) ≤ γ a j - γ b j := by
      rw [abs_of_nonneg (sub_nonneg.mpr hba)] at hdiam
      exact hdiam
    obtain ⟨k₀, hkpos, hksize, hb, ha⟩ :=
      Q.exists_prefixes_between_vertices j width N hwidth (hγ.mem_region b) (hγ.mem_region a) hgap
    exact ⟨j, k₀, hkpos, hksize, ⟨b, hb⟩, ⟨a, ha⟩⟩

/-- Uniform slab two-point bounds control the probability that a path of
large coordinate diameter is disconnected from a cube-crossing component. -/
theorem IntegerCube.measureReal_disconnected_large_path_le_of_twoPoint_slabs {d : ℕ}
    (Q : IntegerCube d) (width N : ℕ) (hwidth : 0 < width) (p : unitInterval)
    (ρ : ℝ) (hρ : ρ ≤ 1)
    (hprob : ∀ j : Fin d, ∀ k : ℕ, (k + 1) * width ≤ Q.size →
      ∀ x ∈ Q.slab j width k, ∀ y ∈ Q.slab j width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab j width k)).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ∃ root,
      IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) root ∧
      ∃ n γ, IsSelectedOpenPath ω Q.vertices
        (pathDiameterAtLeast (((N + 1) * width : ℕ) : ℤ)) n γ ∧
        ¬ (openIn ω Q.vertices).Reachable root (γ 0)} ≤
      ((d * Q.size : ℕ) : ℝ) * ((Q.vertices.card : ℝ) ^ 2 *
        (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N) := by
  classical
  let large := pathDiameterAtLeast (d := d) (((N + 1) * width : ℕ) : ℤ)
  let E : Fin d × Fin Q.size → Set (Configuration d) := fun jk => {ω |
    0 < jk.2.val * width ∧ (jk.2.val + N) * width < Q.size ∧
    ∃ root, IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
      (fun i => ↑(Q.upperFace i)) root ∧
      ∃ n γ, IsSelectedOpenPath ω Q.vertices large n γ ∧
        (∃ a, γ a ∈ Q.slabPrefix jk.1 width jk.2.val) ∧
        (∃ b, γ b ∉ Q.slabPrefix jk.1 width (jk.2.val + N)) ∧
        ¬ (openIn ω Q.vertices).Reachable root (γ 0)}
  have hq : 0 ≤ 1 - (p : ℝ) * ((p : ℝ) * ρ) := by
    have hfirst : (p : ℝ) * ρ ≤ 1 := by
      calc
        (p : ℝ) * ρ ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hρ p.property.1
        _ ≤ 1 := by simpa using p.property.2
    have hsecond : (p : ℝ) * ((p : ℝ) * ρ) ≤ 1 := by
      calc
        (p : ℝ) * ((p : ℝ) * ρ) ≤ (p : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hfirst p.property.1
        _ ≤ 1 := by simpa using p.property.2
    exact sub_nonneg.mpr hsecond
  have hbound : ∀ jk, (latticeBondLaw d p).real (E jk) ≤
      (Q.vertices.card : ℝ) ^ 2 * (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N := by
    intro ⟨j, k⟩
    by_cases hk : 0 < k.val * width ∧ (k.val + N) * width < Q.size
    · have hsize : ∀ n ≤ N, (k.val + n) * width < Q.size := by
        intro n hn
        have hmul := Nat.mul_le_mul_right width (Nat.add_le_add_left hn k.val)
        exact lt_of_le_of_lt hmul hk.2
      have hlocal : ∀ n < N, ∀ x ∈ Q.slab j width (k.val + n),
          ∀ y ∈ Q.slab j width (k.val + n), ρ ≤ (latticeBondLaw d p).real
            {ω | (openIn ω (Q.slab j width (k.val + n))).Reachable x y} := by
        intro n hn
        apply hprob j (k.val + n)
        have hnle : k.val + n + 1 ≤ k.val + N := by omega
        exact (Nat.mul_le_mul_right width hnle).trans (Nat.le_of_lt hk.2)
      have hcard : ((Q.vertices.filter fun x => x ∈ Q.slabPrefix j width k.val).card : ℝ) ≤
          Q.vertices.card := by
        exact_mod_cast Finset.card_filter_le _ _
      have hevent := Q.measureReal_disconnected_path_spanning_prefixes_le j width k.val N
        hwidth hk.1 hsize large p ρ hρ hlocal
      calc
        (latticeBondLaw d p).real (E (j, k)) ≤
            ((Q.vertices.filter fun x => x ∈ Q.slabPrefix j width k.val).card : ℝ) ^ 2 *
              (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N := by
          apply (measureReal_mono ?_ (measure_ne_top _ _)).trans hevent
          intro ω hω
          exact hω.2.2
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (pow_nonneg hq N)
    · have hempty : E (j, k) = ∅ := by
        ext ω
        simp only [E, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hk ⟨h.1, h.2.1⟩
      rw [hempty, measureReal_empty]
      exact mul_nonneg (sq_nonneg _) (pow_nonneg hq N)
  have hcover : {ω | ∃ root,
      IsCrossingRoot ω Q.vertices (fun i => ↑(Q.lowerFace i))
        (fun i => ↑(Q.upperFace i)) root ∧
      ∃ n γ, IsSelectedOpenPath ω Q.vertices large n γ ∧
        ¬ (openIn ω Q.vertices).Reachable root (γ 0)} ⊆ ⋃ jk, E jk := by
    rintro ω ⟨root, hroot, n, γ, hγ, hsep⟩
    obtain ⟨j, k₀, hkpos, hksize, ha, hb⟩ :=
      Q.exists_prefixes_spanned_by_path width N hwidth hγ
    have hksize' : k₀ < Q.size := by nlinarith
    exact Set.mem_iUnion.mpr ⟨(j, ⟨k₀, hksize'⟩), hkpos, hksize,
      root, hroot, n, γ, hγ, ha, hb, hsep⟩
  calc
    _ ≤ (latticeBondLaw d p).real (⋃ jk, E jk) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ jk, (latticeBondLaw d p).real (E jk) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _jk : Fin d × Fin Q.size,
        ((Q.vertices.card : ℝ) ^ 2 * (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N) :=
      Finset.sum_le_sum fun jk _ => hbound jk
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]

end Rigidity.Percolation
