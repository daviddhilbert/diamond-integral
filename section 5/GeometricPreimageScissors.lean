import «section 5».GeometricPreimagePartitions
import «section 5».DiagonalGeometricUnit

/-! The inverse value respects actual closed/open scissors and every
geometric unit presentation. All isomorphisms are over the complex base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal

theorem geometricPreimage_scissor (X Y Z : EquivariantVariety.Object)
    (i : Morphism Y X) (j : Morphism Z X) (hi : IsClosedImmersion i.hom) (hj : IsOpenImmersion j.hom)
    (hcomp : Set.range j.hom = (Set.range i.hom)ᶜ) :
    geometricPreimage X = geometricPreimage Y + geometricPreimage Z := by
  letI := hi
  letI := hj
  let K : Bool → EquivariantVariety.Object := fun | false => Y | true => Z
  let k : ∀ b : Bool, Morphism (K b) X := fun | false => i | true => j
  letI : ∀ b : Bool, IsImmersion (k b).hom := by
    intro b
    cases b
    · exact inferInstanceAs (IsImmersion i.hom)
    · exact inferInstanceAs (IsImmersion j.hom)
  have hh := geometricPreimage_finite_partition X K k (by
    intro x
    by_cases hx : x ∈ Set.range i.hom
    · refine ⟨false, hx, ?_⟩
      intro b hb
      cases b
      · rfl
      · have hb' : x ∈ Set.range j.hom := hb
        rw [hcomp] at hb'
        exact False.elim (hb' hx)
    · have hy : x ∈ Set.range j.hom := hcomp.superset hx
      refine ⟨true, hy, ?_⟩
      intro b hb
      cases b
      · exact False.elim (hx hb)
      · rfl)
  simpa [K, add_comm] using hh

def geometricUnitIso (X : EquivariantVariety.Object) (hX : IsIso X.toC) :
    EquivariantVariety.Iso X (rationalAffineObject (Fin.elim0 : Fin 0 → ℚ)) := by
  let U := rationalAffineObject (Fin.elim0 : Fin 0 → ℚ)
  letI := hX
  letI : IsIso U.toC := rationalAffineObject_zero_toC_isIso
  let e := asIso X.toC ≪≫ (asIso U.toC).symm
  have he : e.hom ≫ U.toC = X.toC := by
    dsimp only [e, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom, asIso_hom, asIso_inv]
    simp
  exact {
    iso := e
    overC := he
    equivariant := fun h => by
      apply (cancel_mono U.toC).mp
      calc
        ((X.action h).asIso.hom ≫ e.hom) ≫ U.toC = (X.action h).asIso.hom ≫ X.toC := by
          rw [Category.assoc, he]
        _ = X.toC := X.overC h
        _ = e.hom ≫ U.toC := he.symm
        _ = (e.hom ≫ (U.action h).asIso.hom) ≫ U.toC := by rw [Category.assoc, U.overC] }

theorem geometricPreimage_affine_zero : geometricPreimage (rationalAffineObject (Fin.elim0 : Fin 0 → ℚ)) = 1 := by
  let U := rationalAffineObject (Fin.elim0 : Fin 0 → ℚ)
  let f := Morphism.id U
  letI : IsImmersion f.hom := inferInstanceAs (IsImmersion (𝟙 U.scheme))
  let A := DiagonalConstructible.immersedObject (Fin.elim0 : Fin 0 → ℚ) f
  have hA : A.domain = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨complexTupleSpectrumPoint x, rfl⟩
  have hc : DiagonalConstructible.objectClass A = 1 :=
    (DiagonalConstructible.setClass_congr (Fin.elim0 : Fin 0 → ℚ) A.domain Set.univ
      A.definable A.invariant DiagonalConstructible.unit.definable DiagonalConstructible.unit.invariant hA).trans
      DiagonalConstructible.objectClass_unit
  exact (geometricPreimage_of_immersion (Fin.elim0 : Fin 0 → ℚ) f).trans hc

theorem geometricPreimage_unit (X : EquivariantVariety.Object) (hX : IsIso X.toC) : geometricPreimage X = 1 :=
  (geometricPreimage_iso (geometricUnitIso X hX)).trans geometricPreimage_affine_zero

end DiamondIntegral.Section5
