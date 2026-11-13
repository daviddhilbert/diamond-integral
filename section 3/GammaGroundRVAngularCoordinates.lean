import «section 3».RVAngularCoordinateMaps
import «section 3».GammaGroundMapImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)}
def rvAngularGlobalCoordinateMap (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active)) (S : Set M) :
    Map (DefSet.univ (rawRVUnitSpace (M := M) n) S) (DefSet.univ ((rawRVUnitSpace K.zeroArity).prod (rawRVUnitSpace K.freeArity)) S) := by
  let F := rvAngularCoordinateCode E K
  let f := E.coordinateEquiv K
  have hCode (c : (rawRVUnitSpace (M := M) n).domain) : F c.val =
      Sum.elim (rvUnitValues (f ((rawRVUnitSpace n).decode c)).1) (rvUnitValues (f ((rawRVUnitSpace n).decode c)).2) := by
    have hh := rvAngularCoordinateCode_values E K ((rawRVUnitSpace n).decode c)
    rwa [rvUnitValues_decode] at hh
  have hdom (c : (rawRVUnitSpace (M := M) n).domain) : F c.val ∈
      ((rawRVUnitSpace (M := M) K.zeroArity).prod (rawRVUnitSpace K.freeArity)).domain := by
    change (F c.val ∘ Sum.inl ∈ (rawRVUnitSpace K.zeroArity).domain) ∧
      (F c.val ∘ Sum.inr ∈ (rawRVUnitSpace K.freeArity).domain)
    rw [hCode c]
    exact ⟨Set.mem_range_self _,Set.mem_range_self _⟩
  refine Map.ofCodes _ f F (rvAngularCoordinateCode_definable E K S) hdom ?_
  intro c
  apply Prod.ext
  · apply rvUnitValues_injective
    exact (rvUnitValues_decode _).trans
      (congrArg (fun z : Fin K.zeroArity ⊕ Fin K.freeArity → M => z ∘ Sum.inl) (hCode c))
  · apply rvUnitValues_injective
    exact (rvUnitValues_decode _).trans
      (congrArg (fun z : Fin K.zeroArity ⊕ Fin K.freeArity → M => z ∘ Sum.inr) (hCode c))


def gammaGroundRVAngularCoordinateMap {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    GammaGroundMap X (GammaGroundDefSet.univ hc B ((rawRVUnitSpace K.zeroArity).prod (rawRVUnitSpace K.freeArity))) :=
  GammaGroundMap.ofGlobal _ _ (rvAngularGlobalCoordinateMap E K B.real) (fun _ => Set.mem_univ _)

theorem gammaGroundRVAngularCoordinateMap_injective {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    Function.Injective (gammaGroundRVAngularCoordinateMap X E K) := by
  intro x y he
  apply Subtype.ext
  exact (E.coordinateEquiv K).injective (congrArg (fun z : GammaGroundDefSet.univ hc B ((rawRVUnitSpace K.zeroArity).prod (rawRVUnitSpace K.freeArity)) => z.val) he)

theorem gammaGroundRVAngularCoordinateMap_image {hc : CanonicalStructure.IsCanonical (M := M)}
    {B : GammaParameters.Base (M := M)}
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (gammaGroundRVAngularCoordinateMap X E K).image.carrier = E.coordinateImage K := by
  ext y
  exact ⟨fun ⟨x,hx⟩ => ⟨x.val,x.property,hx⟩,fun ⟨x,hx,he⟩ => ⟨⟨x,hx⟩,he⟩⟩
end DiamondIntegral.Section3
