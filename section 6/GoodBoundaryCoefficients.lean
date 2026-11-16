import «section 6».PairedBoundaryData

/-! The set of coefficients matching every exceptional core is defined
over the original base by projecting the actual bad parameter pairs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def badBoundaryParameters (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) :
    DefSet ((rawMixedSpace (M := M) 1 r).prod (rawVFSpace 1)) S := by
  refine ⟨{x | ∃ z : E.prod (positiveBoundaryCoefficients hc),z.val=x ∧
    uniformBoundaryCoreCodes hc f E hEA hRV hD z ∉ parameterizedPairedDiscCodes (unaryMixedScalarGraph f)},?_⟩
  have hd := (uniformPairedBoundaryDataMap hc f E hEA hRV hD).definable_preimage
    (goodPairedBoundaryData (unaryMixedScalarGraph f) (unaryMixedScalarGraph_definable f)).definable.compl
  convert hd using 1
  ext x
  constructor
  · rintro ⟨z,rfl,hz⟩
    refine ⟨z,rfl,?_⟩
    change pairedBoundaryDataCodes _ ∉ parameterizedPairedDiscCodes (unaryMixedScalarGraph f)
    rwa [uniformPairedBoundaryDataMap_codes]
  · rintro ⟨z,rfl,hz⟩
    refine ⟨z,rfl,?_⟩
    change pairedBoundaryDataCodes _ ∉ parameterizedPairedDiscCodes (unaryMixedScalarGraph f) at hz
    rwa [uniformPairedBoundaryDataMap_codes] at hz

def badBoundaryCoefficientMap (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) :=
  Map.snd (rawMixedSpace (M := M) 1 r) (rawVFSpace 1) S (badBoundaryParameters hc f E hEA hRV hD)

def goodBoundaryCoefficients (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) : DefSet (rawVFSpace (M := M) 1) S :=
  ⟨(positiveBoundaryCoefficients hc).carrier ∩ (badBoundaryCoefficientMap hc f E hEA hRV hD).image.carrierᶜ,
    (positiveBoundaryCoefficients hc).definable.inter (rawVFSpace 1)
      (badBoundaryCoefficientMap hc f E hEA hRV hD).image.definable.compl⟩

theorem goodBoundaryCoefficients_iff (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (c : positiveBoundaryCoefficients (S := S) hc) :
    c.val ∈ (goodBoundaryCoefficients hc f E hEA hRV hD).carrier ↔ uniformBoundaryCoreGood hc f E hEA hRV hD c := by
  constructor
  · rintro ⟨hcPos,hcGood⟩ p
    by_contra hn
    let z := boundaryPairInput hc E p c
    let b : badBoundaryParameters hc f E hEA hRV hD := ⟨z.val,z,rfl,hn⟩
    exact hcGood ⟨b,rfl⟩
  · intro hGood
    refine ⟨c.property,?_⟩
    rintro ⟨b,hb⟩
    obtain ⟨z,hz,hBad⟩ := b.property
    have hCoeff : z.val.2=c.val := (congrArg Prod.snd hz).trans hb
    let p : E := ⟨z.val.1,z.property.1⟩
    have hEq : z=boundaryPairInput hc E p c := Subtype.ext (Prod.ext rfl hCoeff)
    exact hBad (hEq ▸ hGood p)

end DiamondIntegral.Section6
