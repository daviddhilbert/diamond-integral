import «section 6».UniformBoundaryConditions
import «section 6».ScalarGammaValues

/-! The actual bad paired-boundary parameters give a full definable
positive Gamma relation over the original centre family. Its projections
and row bounds are constructed before the uniform RV-family estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.BoundaryBadGamma
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
variable (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
variable (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
variable (D : DefSet (pairedBoundaryDataSpace M (r+s)) S)

abbrev domain := badBoundaryDataParameters hc f E hEA hRV hD D

def centre : Map (domain hc f E hEA hRV hD D) E :=
  (Map.fst (rawMixedSpace (M := M) 1 r) (rawVFSpace 1) S (domain hc f E hEA hRV hD D)).corestrict (by
    intro b
    obtain ⟨z,hz,hBad⟩ := b.property
    have hPoint := congrArg Prod.fst hz
    change b.val.1 ∈ E.carrier
    exact hPoint ▸ z.property.1)

def coefficient : Map (domain hc f E hEA hRV hD D) (positiveBoundaryCoefficients (S := S) hc) :=
  (Map.snd (rawMixedSpace (M := M) 1 r) (rawVFSpace 1) S (domain hc f E hEA hRV hD D)).corestrict (by
    intro b
    obtain ⟨z,hz,hBad⟩ := b.property
    have hPoint := congrArg Prod.snd hz
    change b.val.2 ∈ (positiveBoundaryCoefficients (S := S) hc).carrier
    exact hPoint ▸ z.property.2)

def valueMap := (scalarGammaValueMap S).comp (coefficient hc f E hEA hRV hD D).toUniv

def map := ((centre hc f E hEA hRV hD D).toUniv).pair (valueMap hc f E hEA hRV hD D)

def relation := (map hc f E hEA hRV hD D).image

theorem valueMap_value (b : domain hc f E hEA hRV hD D) :
    gammaMapValue (valueMap hc f E hEA hRV hD D) b=
      finiteValue (((coefficient hc f E hEA hRV hD D) b).val 0)
        (((coefficient hc f E hEA hRV hD D) b).property.1) := by
  apply Subtype.ext
  exact scalarGammaValueMap_nonzero S ((coefficient hc f E hEA hRV hD D) b).val
    ((coefficient hc f E hEA hRV hD D) b).property.1

theorem bad (b : domain hc f E hEA hRV hD D) :
    (uniformPairedBoundaryDataMap hc f E hEA hRV hD
      (boundaryPairInput hc E ((centre hc f E hEA hRV hD D) b)
        ((coefficient hc f E hEA hRV hD D) b))).val ∉ D.carrier := by
  obtain ⟨z,hz,hBad⟩ := b.property
  have he : boundaryPairInput hc E ((centre hc f E hEA hRV hD D) b)
      ((coefficient hc f E hEA hRV hD D) b)=z := Subtype.ext hz.symm
  rw [he]
  exact hBad

theorem mem_relation_iff (p : Mixed M 1 r) (γ : Gamma M) :
    (p,γ) ∈ (relation hc f E hEA hRV hD D).carrier ↔
      ∃ b : domain hc f E hEA hRV hD D,
        ((centre hc f E hEA hRV hD D) b).val=p ∧ gammaMapValue (valueMap hc f E hEA hRV hD D) b=γ := by
  constructor
  · rintro ⟨b,hb⟩
    change (((centre hc f E hEA hRV hD D) b).val,gammaMapValue (valueMap hc f E hEA hRV hD D) b)=(p,γ) at hb
    have hp := congrArg Prod.fst hb
    have hγ := congrArg Prod.snd hb
    exact ⟨b,hp,hγ⟩
  · rintro ⟨b,hp,hγ⟩
    exact ⟨b,Prod.ext hp hγ⟩

theorem source (z) (hz : z ∈ (relation hc f E hEA hRV hD D).carrier) : z.1 ∈ E.carrier := by
  obtain ⟨b,hb⟩ := hz
  have h := congrArg Prod.fst hb
  exact h ▸ ((centre hc f E hEA hRV hD D) b).property

theorem positive (p : Mixed M 1 r) (γ : Gamma M)
    (h : (p,γ) ∈ (relation hc f E hEA hRV hD D).carrier) : 1≤γ := by
  obtain ⟨b,hbp,hbγ⟩ := (mem_relation_iff hc f E hEA hRV hD D p γ).mp h
  rw [← hbγ,valueMap_value]
  have h' : (1 : Gamma M)<finiteValue (((coefficient hc f E hEA hRV hD D) b).val 0)
      (((coefficient hc f E hEA hRV hD D) b).property.1) :=
    ((coefficient hc f E hEA hRV hD D) b).property.2
  exact h'.le

theorem row_bddAbove (p : E)
    (hEventual : ∃ η : Gamma M,∀ c : positiveBoundaryCoefficients (S := S) hc,
      η.val<vfValue (c.val 0) →
      (uniformPairedBoundaryDataMap hc f E hEA hRV hD (boundaryPairInput hc E p c)).val ∈ D.carrier) :
    BddAbove {γ : Gamma M | (p.val,γ) ∈ (relation hc f E hEA hRV hD D).carrier} := by
  obtain ⟨η,hη⟩ := hEventual
  refine ⟨η,fun γ hγ => ?_⟩
  obtain ⟨b,hbp,hbγ⟩ := (mem_relation_iff hc f E hEA hRV hD D p.val γ).mp hγ
  have hp : (centre hc f E hEA hRV hD D) b=p := Subtype.ext hbp
  by_contra hn
  have hSmall : η.val<vfValue (((coefficient hc f E hEA hRV hD D) b).val 0) := by
    have hFinite : η<finiteValue (((coefficient hc f E hEA hRV hD D) b).val 0)
        (((coefficient hc f E hEA hRV hD D) b).property.1) := by
      rw [← valueMap_value,hbγ]
      exact lt_of_not_ge hn
    exact hFinite
  have hBad := bad hc f E hEA hRV hD D b
  rw [hp] at hBad
  exact hBad (hη ((coefficient hc f E hEA hRV hD D) b) hSmall)

end DiamondIntegral.Section6.BoundaryBadGamma
