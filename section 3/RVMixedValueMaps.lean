import «section 3».RVUnitGammaMaps
import Section4.MapProduct
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p m : ℕ}

def rvMixedValueProjectionMap (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet ((rawRVUnitSpace (M := M) p).prod (rawRVUnitSpace m)) S) :
    Map X (DefSet.univ ((rawRVUnitSpace p).prod ((volumeGammaSpace hc).power (Fin m))) S) :=
  ((Map.fst (rawRVUnitSpace p) (rawRVUnitSpace m) S X).pair
    ((rvUnitGammaMap hc S m).comp (Map.snd (rawRVUnitSpace p) (rawRVUnitSpace m) S X))).toUniv

theorem rvMixedValueProjectionMap_values (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet ((rawRVUnitSpace (M := M) p).prod (rawRVUnitSpace m)) S) (x : X) :
    (rvMixedValueProjectionMap hc X x).val = mixedValueProjection rvUnitTupleValues x.val := rfl

theorem rvMixedValueProjectionMap_image (hc : CanonicalStructure.IsCanonical (M := M))
    (X : DefSet ((rawRVUnitSpace (M := M) p).prod (rawRVUnitSpace m)) S) :
    (rvMixedValueProjectionMap hc X).image.carrier = mixedValueQuotient rvUnitTupleValues X.carrier := by
  ext y
  exact ⟨fun ⟨x,hx⟩ => ⟨x.val,x.property,hx⟩,fun ⟨x,hx,he⟩ => ⟨⟨x,hx⟩,he⟩⟩

theorem mixedValueQuotient_residue_projection {R T V : Type} (v : T → V) (A : Set (R × T)) :
    Prod.fst '' mixedValueQuotient v A = Prod.fst '' A := by
  ext r
  constructor
  · rintro ⟨⟨s,γ⟩,⟨⟨u,t⟩,ht,he⟩,hs⟩
    refine ⟨(u,t),ht,?_⟩
    exact (congrArg Prod.fst he).trans hs
  · rintro ⟨⟨s,t⟩,ht,hs⟩
    exact ⟨(s,v t),⟨(s,t),ht,rfl⟩,hs⟩
end DiamondIntegral.Section3
