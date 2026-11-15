module
public import «section 5».ValueInducedRectangles

/-!
# Pulling the finite value partition back through a coordinate equivalence

The coordinate equivalence in the ACVF application is integral monomial.
This file proves the geometric assembly for any equivalence compatible
with the value maps. Its hypotheses are explicit rectangle data, rather
than an assumed version of Lemma 5.12. The ACVF definability and original-
ground descent adapters are still needed before this proves that lemma.
-/

set_option autoImplicit false
@[expose] public section
namespace DiamondIntegral.Section5
noncomputable section
open Set

variable {Z R Y V G I : Type*}

theorem equiv_image_value_cut
    (e : Z ≃ R × Y) (w : Z → V × G) (a : R → V) (v : Y → G)
    (hw : ∀ z, Prod.map a v (e z) = w z) (X : Set Z) (D : Set (V × G)) :
    e '' (X ∩ w ⁻¹' D) = (e '' X) ∩ Prod.map a v ⁻¹' D := by
  ext q
  constructor
  · rintro ⟨z, ⟨hx, hd⟩, rfl⟩
    refine ⟨⟨z, hx, rfl⟩, ?_⟩
    change Prod.map a v (e z) ∈ D
    rw [hw]
    exact hd
  · rintro ⟨⟨z, hx, rfl⟩, hd⟩
    refine ⟨z, ⟨hx, ?_⟩, rfl⟩
    change w z ∈ D
    change Prod.map a v (e z) ∈ D at hd
    rwa [hw] at hd

/-- Geometry of the value-induced pieces, with the *original* value map
on the source. This structure intentionally contains no definability claim. -/
structure ValueInducedChartPiece
    (X : Set Z) (e : Z ≃ R × Y) (w : Z → V × G) (a : R → V) (v : Y → G) where
  values : Set (V × G)
  values_subset : values ⊆ w '' X
  residue : Set R
  gamma : Set G
  activeValue : V
  residue_value : a '' residue ⊆ {activeValue}
  chart_eq : e '' (X ∩ w ⁻¹' values) = residue.prod (v ⁻¹' gamma)

/-- Finite value-induced assembly of a rectangle cover in monomial
coordinates. Residue factors with the same active value are consolidated
on a common Boolean refinement of all Gamma supports. -/
theorem finite_valueInduced_chart_partition [Fintype I]
    (e : Z ≃ R × Y) (w : Z → V × G) (a : R → V) (v : Y → G)
    (hw : ∀ z, Prod.map a v (e z) = w z) (X : Set Z)
    (residues : I → Set R) (supports : I → Set G)
    (hX : ∀ z, z ∈ X ↔ ∃ i, (e z).1 ∈ residues i ∧ v (e z).2 ∈ supports i)
    (hfinite : ∀ i, (a '' residues i).Finite) :
    ∃ N : ℕ, ∃ C : Fin N → ValueInducedChartPiece X e w a v,
      (∀ j k, j ≠ k → Disjoint (C j).values (C k).values) ∧
      (∀ q, q ∈ w '' X ↔ ∃ j, q ∈ (C j).values) ∧
      (∀ z, z ∈ X ↔ ∃ j, z ∈ X ∩ w ⁻¹' (C j).values) := by
  classical
  have himage : ∀ r y, (r, y) ∈ e '' X ↔
      ∃ i, r ∈ residues i ∧ v y ∈ supports i := by
    intro r y
    constructor
    · rintro ⟨z, hz, he⟩
      simpa only [he] using (hX z).mp hz
    · intro h
      refine ⟨e.symm (r, y), (hX _).mpr ?_, e.apply_symm_apply _⟩
      simpa only [e.apply_symm_apply] using h
  have hvalues : Prod.map a v '' (e '' X) = w '' X := by
    ext q
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, he⟩
      exact ⟨z, hz, (hw z).symm.trans he⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e z, ⟨z, hz, rfl⟩, hw z⟩
  obtain ⟨N, β, s, hdis, hcov, hrect, hfixed, _hactive⟩ :=
    finite_valueInduced_rectangle_partition a v (e '' X) residues supports himage hfinite
  let C : Fin N → ValueInducedChartPiece X e w a v := fun j => {
    values := rectangleValueCell a v (e '' X) supports (β j) (s j)
    values_subset := fun q hq => hvalues ▸ hq.1
    residue := rectangleResidueCell a residues (β j) (s j)
    gamma := rectangleGammaCell a v (e '' X) supports (β j) (s j)
    activeValue := β j
    residue_value := hfixed j
    chart_eq := (equiv_image_value_cut e w a v hw X _).trans (hrect j)
  }
  refine ⟨N, C, hdis, ?_, ?_⟩
  · intro q
    rw [← hvalues]
    exact hcov q
  · intro z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := (hcov (w z)).mp (hvalues.symm ▸ ⟨z, hz, rfl⟩)
      exact ⟨j, hz, hj⟩
    · rintro ⟨j, hz, _⟩
      exact hz

end
end DiamondIntegral.Section5
