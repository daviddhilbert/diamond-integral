import «section 6».RestoredActiveSteps

/-! An active full-disc step can be performed after an arbitrary
retained bounded unit base homeomorphism and then pulled back through
the actual inverse base map. The complete result fixes every inactive
VF coordinate, with no RV-constant displacement assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RetainedUnitBaseMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def conjugateActive
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnitBaseMap (G := G) A) (k : Fin r)
    (D : CentripetalData (G := G) (rvCoordinateBundle F.target (F.labels k)))
    (hCoord : D.coordinate=Fin.last n) : RetainedUnitBaseMap (G := G) (rvCoordinateBundle A k) := by
  have hA := F.home.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  let R₀ := identity h00 hc linear hκ hs hv hsmall hΓ hA F.sourceBounded
  let R := R₀.pullback h00 hc linear hκ hs hv hsmall hΓ F.map F.home F.targetBounded F.unit
  let G := F.carry h00 hc linear hκ hs hv hsmall hΓ k
  let H := R.restoreActive h00 hc linear hκ hs hv hsmall hΓ (F.labels k) D hCoord
  exact G.comp h00 hc linear hκ hs hv hsmall hΓ H

theorem conjugateActive_fixes_base
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnitBaseMap (G := G) A) (k : Fin r)
    (D : CentripetalData (G := G) (rvCoordinateBundle F.target (F.labels k)))
    (hCoord : D.coordinate=Fin.last n) (p : rvCoordinateBundle A k) :
    Fin.init ((F.conjugateActive h00 hc linear hκ hs hv hsmall hΓ k D hCoord).map p).val.1=Fin.init p.val.1 := by
  have hA := F.home.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  let R₀ := identity h00 hc linear hκ hs hv hsmall hΓ hA F.sourceBounded
  let R := R₀.pullback h00 hc linear hκ hs hv hsmall hΓ F.map F.home F.targetBounded F.unit
  let G := F.carry h00 hc linear hκ hs hv hsmall hΓ k
  change Fin.init ((R.restoreActive h00 hc linear hκ hs hv hsmall hΓ (F.labels k) D hCoord).map (G.map p)).val.1=_
  rw [restoreActive_base_value]
  change (R.map (bundleProjection F.target (F.labels k)
    (carryLastMap F.map k (F.labels k) (fun p => F.retained p k) p))).val.1=_
  rw [carryLastMap_base]
  exact R₀.pullback_restores h00 hc linear hκ hs hv hsmall hΓ F.map F.home F.targetBounded F.unit (bundleProjection A k p)

theorem conjugateActive_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnitBaseMap (G := G) A) (k : Fin r)
    (D : CentripetalData (G := G) (rvCoordinateBundle F.target (F.labels k)))
    (hCoord : D.coordinate=Fin.last n) :
    let H := F.conjugateActive h00 hc linear hκ hs hv hsmall hΓ k D hCoord
    ∃ C : RetainedUnaryHomeChain (G := G) S H.map H.labels,C.DoublyBounded := by
  let H := F.conjugateActive h00 hc linear hκ hs hv hsmall hΓ k D hCoord
  let C : RetainedUnaryHomeChain (G := G) S H.map H.labels :=
    .unary (Fin.last n) H.home
      (by
        intro p i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro hi
          exact False.elim (hi rfl)
        · intro _
          exact congrFun (F.conjugateActive_fixes_base h00 hc linear hκ hs hv hsmall hΓ k D hCoord p) j)
      H.unit H.retained
  exact ⟨C,H.sourceBounded,H.targetBounded⟩

end DiamondIntegral.Section6.RetainedUnitBaseMap
