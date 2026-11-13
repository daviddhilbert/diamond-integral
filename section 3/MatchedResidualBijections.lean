import «section 3».TensorProductCuts
import «section 3».GammaGroundRVFinitePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M} {A0 : GammaGroundDefSet hc B P} {B0 : GammaGroundDefSet hc B Q}
variable {ι : Type} {U V : ι → Space LRV M}
variable {D : ∀ i, GammaGroundDefSet hc B (U i)} {E : ∀ i, GammaGroundDefSet hc B (V i)}

/-- Actual matched image bijections carry ambient disjointness from
source to target. The chart spaces may have different tuple arities. -/
theorem gammaGroundMatchedImages_disjoint
    (F : GammaGroundBijection A0 B0) (e : ∀ i, GammaGroundBijection (D i) (E i))
    (a : ∀ i, GammaGroundMap (D i) A0) (b : ∀ i, GammaGroundMap (E i) B0)
    (hgraph : ∀ i u, b i ((e i).map u) = F.map (a i u)) (i j : ι)
    (hd : Disjoint (a i).image.carrier (a j).image.carrier) :
    Disjoint (b i).image.carrier (b j).image.carrier := by
  apply Set.disjoint_left.mpr
  rintro z ⟨v,hv⟩ ⟨w,hw⟩
  obtain ⟨u,rfl⟩ := (e i).bijective.2 v
  obtain ⟨u',rfl⟩ := (e j).bijective.2 w
  have he : b i ((e i).map u) = b j ((e j).map u') := Subtype.ext (hv.trans hw.symm)
  rw [hgraph,hgraph] at he
  have hs := F.bijective.1 he
  have h1 : (a i u).val ∈ (a i).image.carrier := ⟨u,rfl⟩
  have h2 : (a i u).val ∈ (a j).image.carrier := ⟨u',(congrArg (fun x : A0 => x.val) hs).symm⟩
  exact Set.disjoint_left.mp hd h1 h2

/-- A finite family of matches identifies the actual ambient source
union with the preimage of the actual ambient target union. -/
theorem gammaGroundMatchedImages_preimage_union [Fintype ι]
    (F : GammaGroundBijection A0 B0) (e : ∀ i, GammaGroundBijection (D i) (E i))
    (a : ∀ i, GammaGroundMap (D i) A0) (b : ∀ i, GammaGroundMap (E i) B0)
    (hgraph : ∀ i u, b i ((e i).map u) = F.map (a i u)) :
    F.inverseImage (gammaGroundDefSetFiniteUnion Finset.univ (fun i => (b i).image)) =
      gammaGroundDefSetFiniteUnion Finset.univ (fun i => (a i).image) := by
  apply gammaGroundDefSet_eq_of_carrier_eq
  ext x
  constructor
  · rintro ⟨p,hpx,i,hi,v,hv⟩
    obtain ⟨u,hu⟩ := (e i).bijective.2 v
    have hv' : (b i ((e i).map u)).val = (F.map p).val :=
      (congrArg (fun z : E i => (b i z).val) hu).trans hv
    have hF : (F.map (a i u)).val = (F.map p).val :=
      (congrArg (fun z : B0 => z.val) (hgraph i u)).symm.trans hv'
    have hs := F.bijective.1 (Subtype.ext hF)
    exact ⟨i,hi,u,(congrArg (fun z : A0 => z.val) hs).trans hpx⟩
  · rintro ⟨i,hi,u,hu⟩
    exact ⟨a i u,hu,i,hi,(e i).map u,congrArg (fun z : B0 => z.val) (hgraph i u)⟩

/-- A source-union refinement covers every original matched target.
This keeps the inverse generic cover after disjoint source selection. -/
theorem gammaGroundMatchedImages_target_subset_union [Fintype ι]
    (F : GammaGroundBijection A0 B0) (e : ∀ i, GammaGroundBijection (D i) (E i))
    (a : ∀ i, GammaGroundMap (D i) A0) (b : ∀ i, GammaGroundMap (E i) B0)
    (hgraph : ∀ i u, b i ((e i).map u) = F.map (a i u))
    {W Z : Space LRV M} {D0 : GammaGroundDefSet hc B W} {E0 : GammaGroundDefSet hc B Z}
    (e0 : GammaGroundBijection D0 E0) (a0 : GammaGroundMap D0 A0) (b0 : GammaGroundMap E0 B0)
    (hg0 : ∀ u, b0 (e0.map u) = F.map (a0 u))
    (hsource : a0.image.carrier ⊆ (gammaGroundDefSetFiniteUnion Finset.univ (fun i => (a i).image)).carrier) :
    b0.image.carrier ⊆ (gammaGroundDefSetFiniteUnion Finset.univ (fun i => (b i).image)).carrier := by
  rintro x ⟨v,hv⟩
  obtain ⟨u,hu⟩ := e0.bijective.2 v
  obtain ⟨i,hi,u',hs⟩ := hsource (show (a0 u).val ∈ a0.image.carrier from ⟨u,rfl⟩)
  have hsame : a i u' = a0 u := Subtype.ext hs
  have he : b i ((e i).map u') = b0 v :=
    (hgraph i u').trans ((congrArg F.map hsame).trans ((hg0 u).symm.trans (congrArg b0 hu)))
  exact ⟨i,hi,(e i).map u',(congrArg (fun z : B0 => z.val) he).trans hv⟩

/-- Restricting the original RV bijection to the two complements gives
an actual residual bijection. No matched sum is cancelled in a semiring. -/
def gammaGroundMatchedResidualBijection [Fintype ι]
    (F : GammaGroundBijection A0 B0) (e : ∀ i, GammaGroundBijection (D i) (E i))
    (a : ∀ i, GammaGroundMap (D i) A0) (b : ∀ i, GammaGroundMap (E i) B0)
    (hgraph : ∀ i u, b i ((e i).map u) = F.map (a i u)) :
    GammaGroundBijection
      (A0.sdiff (gammaGroundDefSetFiniteUnion Finset.univ (fun i => (a i).image)))
      (B0.sdiff (gammaGroundDefSetFiniteUnion Finset.univ (fun i => (b i).image))) := by
  let S := gammaGroundDefSetFiniteUnion Finset.univ (fun i => (a i).image)
  let T := gammaGroundDefSetFiniteUnion Finset.univ (fun i => (b i).image)
  have hp : F.map.preimage T = S := gammaGroundMatchedImages_preimage_union F e a b hgraph
  have he : F.inverseImage (B0.sdiff T) = A0.sdiff S := by
    change F.map.preimage (B0.sdiff T) = A0.sdiff S
    rw [GammaGroundMap.preimage_target_sdiff,hp]
  exact (F.restrictTarget (B0.sdiff T) (fun _ h => h.1)).comp
    (GammaGroundBijection.ofCarrierEq (congrArg GammaGroundDefSet.carrier he.symm))
end DiamondIntegral.Section3
