import «section 5».VarietyImmersedObjects
import «section 5».ReducedInducedSchemes

/-! Canonical reduced locally closed invariant pieces, and the actual
equivariant identifications of any two reduced immersed presentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] Object.reduced
attribute [local instance] reducedLocallyClosedScheme_isReduced
  reducedLocallyClosedInclusion_isImmersion

def Object.Invariant (X : Object) (S : Set X.scheme) : Prop :=
  ∀ h x, schemePointAction X.action h x ∈ S ↔ x ∈ S

def subsetObject (X : Object) (S : Set X.scheme) (hS : IsLocallyClosed S)
    (hInv : X.Invariant S) : Object :=
  invariantImmersedObject X (reducedLocallyClosedInclusion S hS)
    (by simpa only [reducedLocallyClosedInclusion_range, Object.Invariant] using hInv)

def subsetInclusion (X : Object) (S : Set X.scheme) (hS : IsLocallyClosed S)
    (hInv : X.Invariant S) : Morphism (subsetObject X S hS hInv) X :=
  invariantImmersedInclusion X (reducedLocallyClosedInclusion S hS)
    (by simpa only [reducedLocallyClosedInclusion_range, Object.Invariant] using hInv)

theorem subsetInclusion_range (X : Object) (S : Set X.scheme) (hS : IsLocallyClosed S)
    (hInv : X.Invariant S) : Set.range (subsetInclusion X S hS hInv).hom = S :=
  reducedLocallyClosedInclusion_range S hS

theorem subsetInclusion_immersion (X : Object) (S : Set X.scheme) (hS : IsLocallyClosed S)
    (hInv : X.Invariant S) : IsImmersion (subsetInclusion X S hS hInv).hom :=
  reducedLocallyClosedInclusion_isImmersion S hS

def immersedPresentationIso {X Y Z : Object} (f : Morphism Y X) (g : Morphism Z X)
    [IsImmersion f.hom] [IsImmersion g.hom] (h : Set.range f.hom = Set.range g.hom) : Iso Y Z where
  iso := reducedImmersionIso f.hom g.hom h
  overC := by rw [← g.overC, ← Category.assoc, reducedImmersionIso_fac, f.overC]
  equivariant := reducedImmersionIso_equivariant f.hom g.hom h Y.action Z.action X.action
    f.equivariant g.equivariant

theorem objectClass_immersed_presentations {X Y Z : Object}
    (f : Morphism Y X) (g : Morphism Z X)
    [IsImmersion f.hom] [IsImmersion g.hom] (h : Set.range f.hom = Set.range g.hom) :
    objectClass Y = objectClass Z := objectClass_iso (immersedPresentationIso f g h)

def subsetMorphism (X : Object) {A B : Set X.scheme}
    (hA : IsLocallyClosed A) (hB : IsLocallyClosed B)
    (hiA : X.Invariant A) (hiB : X.Invariant B) (hAB : A ⊆ B) :
    Morphism (subsetObject X A hA hiA) (subsetObject X B hB hiB) := by
  let f := subsetInclusion X A hA hiA
  let g := subsetInclusion X B hB hiB
  letI := subsetInclusion_immersion X B hB hiB
  let L := reducedImmersionLift g.hom f.hom (by
    rw [subsetInclusion_range, subsetInclusion_range]
    exact hAB)
  have hL : L ≫ g.hom = f.hom := reducedImmersionLift_fac _ _ _
  exact {
    hom := L
    overC := by rw [← g.overC, ← Category.assoc, hL, f.overC]
    equivariant := fun h => by
      apply (cancel_mono g.hom).mp
      calc
        (((subsetObject X A hA hiA).action h).asIso.hom ≫ L) ≫ g.hom =
            ((subsetObject X A hA hiA).action h).asIso.hom ≫ f.hom := by
          rw [Category.assoc, hL]
        _ = f.hom ≫ (X.action h).asIso.hom := f.equivariant h
        _ = (L ≫ g.hom) ≫ (X.action h).asIso.hom := by rw [hL]
        _ = L ≫ (g.hom ≫ (X.action h).asIso.hom) := Category.assoc _ _ _
        _ = L ≫ (((subsetObject X B hB hiB).action h).asIso.hom ≫ g.hom) :=
          congrArg (fun m => L ≫ m) (g.equivariant h).symm
        _ = (L ≫ ((subsetObject X B hB hiB).action h).asIso.hom) ≫ g.hom :=
          (Category.assoc _ _ _).symm }

@[reassoc]
theorem subsetMorphism_fac (X : Object) {A B : Set X.scheme}
    (hA : IsLocallyClosed A) (hB : IsLocallyClosed B)
    (hiA : X.Invariant A) (hiB : X.Invariant B) (hAB : A ⊆ B) :
    (subsetMorphism X hA hB hiA hiB hAB).hom ≫ (subsetInclusion X B hB hiB).hom =
      (subsetInclusion X A hA hiA).hom := by
  letI := subsetInclusion_immersion X B hB hiB
  exact reducedImmersionLift_fac (subsetInclusion X B hB hiB).hom
    (subsetInclusion X A hA hiA).hom (by
      rw [subsetInclusion_range, subsetInclusion_range]
      exact hAB)

theorem subsetMorphism_range (X : Object) {A B : Set X.scheme}
    (hA : IsLocallyClosed A) (hB : IsLocallyClosed B)
    (hiA : X.Invariant A) (hiB : X.Invariant B) (hAB : A ⊆ B) :
    Set.range (subsetMorphism X hA hB hiA hiB hAB).hom =
      (subsetInclusion X B hB hiB).hom ⁻¹' A := by
  let f := subsetMorphism X hA hB hiA hiB hAB
  let i := subsetInclusion X A hA hiA
  let j := subsetInclusion X B hB hiB
  letI := subsetInclusion_immersion X B hB hiB
  have hfi : f.hom ≫ j.hom = i.hom := subsetMorphism_fac X hA hB hiA hiB hAB
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    have he := congrArg (fun m => m a) hfi
    change j.hom (f.hom a) = i.hom a at he
    change j.hom (f.hom a) ∈ A
    rw [he]
    exact (subsetInclusion_range X A hA hiA).subset ⟨a, rfl⟩
  · intro hb
    change j.hom b ∈ A at hb
    obtain ⟨a, ha⟩ := (subsetInclusion_range X A hA hiA).superset hb
    refine ⟨a, j.hom.isEmbedding.injective ?_⟩
    have he := congrArg (fun m => m a) hfi
    exact he.trans ha

theorem subsetMorphism_immersion (X : Object) {A B : Set X.scheme}
    (hA : IsLocallyClosed A) (hB : IsLocallyClosed B)
    (hiA : X.Invariant A) (hiB : X.Invariant B) (hAB : A ⊆ B) :
    IsImmersion (subsetMorphism X hA hB hiA hiB hAB).hom := by
  letI := subsetInclusion_immersion X A hA hiA
  haveI : IsImmersion ((subsetMorphism X hA hB hiA hiB hAB).hom ≫
      (subsetInclusion X B hB hiB).hom) := by rw [subsetMorphism_fac]; infer_instance
  exact IsImmersion.of_comp _ (subsetInclusion X B hB hiB).hom

end DiamondIntegral.Section5.EquivariantVariety
