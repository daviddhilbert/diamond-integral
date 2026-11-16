import «section 6».NamedPairedBoundaryCoefficients

/-! Additional original-base conditions on the actual paired-core data
can be imposed before choosing one common named coefficient. -/

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

def badBoundaryDataParameters (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (D : DefSet (pairedBoundaryDataSpace M (r+s)) S) :
    DefSet ((rawMixedSpace (M := M) 1 r).prod (rawVFSpace 1)) S :=
  ⟨{x | ∃ z : E.prod (positiveBoundaryCoefficients hc),z.val=x ∧
    (uniformPairedBoundaryDataMap hc f E hEA hRV hD z).val ∉ D.carrier},
    (uniformPairedBoundaryDataMap hc f E hEA hRV hD).definable_preimage D.definable.compl⟩

def boundaryCoefficientsForData (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (D : DefSet (pairedBoundaryDataSpace M (r+s)) S) : DefSet (rawVFSpace (M := M) 1) S := by
  let bad := (Map.snd (rawMixedSpace (M := M) 1 r) (rawVFSpace 1) S
    (badBoundaryDataParameters hc f E hEA hRV hD D)).image
  exact ⟨(positiveBoundaryCoefficients hc).carrier \ bad.carrier,
    (positiveBoundaryCoefficients hc).definable.sdiff (rawVFSpace 1) bad.definable⟩

theorem boundaryCoefficientsForData_iff (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (D : DefSet (pairedBoundaryDataSpace M (r+s)) S) (c : positiveBoundaryCoefficients (S := S) hc) :
    c.val ∈ (boundaryCoefficientsForData hc f E hEA hRV hD D).carrier ↔
      ∀ p : E,(uniformPairedBoundaryDataMap hc f E hEA hRV hD (boundaryPairInput hc E p c)).val ∈ D.carrier := by
  constructor
  · rintro ⟨hcPos,hcGood⟩ p
    by_contra hn
    let z := boundaryPairInput hc E p c
    let b : badBoundaryDataParameters hc f E hEA hRV hD D := ⟨z.val,z,rfl,hn⟩
    exact hcGood ⟨b,rfl⟩
  · intro hGood
    refine ⟨c.property,?_⟩
    rintro ⟨b,hb⟩
    obtain ⟨z,hz,hBad⟩ := b.property
    have hCoeff : z.val.2=c.val := (congrArg Prod.snd hz).trans hb
    let p : E := ⟨z.val.1,z.property.1⟩
    have hEq : z=boundaryPairInput hc E p c := Subtype.ext (Prod.ext rfl hCoeff)
    exact hBad (hEq ▸ hGood p)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_named_boundary_coefficient_for_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (f : Map A B) (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (D : DefSet (pairedBoundaryDataSpace M (r+s)) S)
    (hEventual : ∃ η : Gamma M,1 ≤ η ∧ ∀ c : positiveBoundaryCoefficients (S := S) hc,
      η.val < vfValue (c.val 0) → ∀ p : E,
        (uniformPairedBoundaryDataMap hc f E hEA hRV hD (boundaryPairInput hc E p c)).val ∈ D.carrier) :
    ∃ (c : VF M) (hc0 : c ≠ 0) (hcPos : (1 : GammaInfinity M) < vfValue c),
      S.Definable₁ LRV {c.val} ∧ ∀ p : E,
        (uniformPairedBoundaryDataMap hc f E hEA hRV hD
          (boundaryPairInput hc E p ⟨(fun _ => c),hc0,hcPos⟩)).val ∈ D.carrier := by
  let C := boundaryCoefficientsForData hc f E hEA hRV hD D
  let P : Set (VF M) := {c | (fun _ : Fin 1 => c) ∈ C.carrier}
  have hP := scalar_vf_defSet_definable C
  obtain ⟨η,hη,hAll⟩ := hEventual
  have hSmall : ∃ ζ : Gamma M,∀ c : VF M,c ≠ 0 → ζ.val < vfValue c → c ∈ P := by
    refine ⟨η,fun c hc0 hcSmall => ?_⟩
    have hPositive : (1 : GammaInfinity M) < vfValue c :=
      (show (1 : GammaInfinity M) ≤ η.val from hη).trans_lt hcSmall
    let c' : positiveBoundaryCoefficients (S := S) hc := ⟨(fun _ => c),hc0,hPositive⟩
    exact (boundaryCoefficientsForData_iff hc f E hEA hRV hD D c').mpr (hAll c' hcSmall)
  obtain ⟨c,hc0,hcDef,hcPos,hGood⟩ := exists_named_vf_in_eventual_property h00 hc hv V hV hVS hSV hnt P hP hSmall
  exact ⟨c,hc0,hcPos,hcDef,(boundaryCoefficientsForData_iff hc f E hEA hRV hD D
    ⟨(fun _ => c),hc0,hcPos⟩).mp hGood⟩

end DiamondIntegral.Section6
