import «section 3».NativeTensorImagePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m : ℕ}
variable {ι J : Type} {P : Space LRV M} {U : GammaGroundDefSet hc B P}

def gammaGroundTensorBoxInParent
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (j : J) (i : {i // tag i = j}) : GammaGroundTensorBox (Y j) (H j) :=
  i.property ▸ E i.val

/-- Inside disjoint parent charts, membership in a union of child
images pulls back to precisely the children with the specified parent.
All parent coordinate spaces and their labels are retained. -/
theorem gammaGroundTensorBox_child_image_pullback [Fintype ι]
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (ht : ∀ j, Function.Injective (t j))
    (hd : ∀ j l, j ≠ l → Disjoint (t j).image.carrier (t l).image.carrier)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (j : J) (x : gammaGroundNativeProductDomain (Y j) (H j)) :
    (t j x).val ∈ (gammaGroundDefSetFiniteUnion Finset.univ
      (fun i => ((t (tag i)).comp (E i).inclusion).image)).carrier ↔
        ∃ i : {i // tag i = j}, x.val ∈ (gammaGroundTensorBoxInParent Y H tag E j i).source.carrier := by
  constructor
  · rintro ⟨i,_,v,hv⟩
    have he : tag i = j := by
      by_contra hn
      have h1 : (t j x).val ∈ (t j).image.carrier := ⟨x,rfl⟩
      have h2 : (t j x).val ∈ (t (tag i)).image.carrier := ⟨(E i).inclusion v,hv⟩
      exact Set.disjoint_left.mp (hd (tag i) j hn) h2 h1
    refine ⟨⟨i,he⟩,?_⟩
    subst j
    have hv' : t (tag i) ((E i).inclusion v) = t (tag i) x := Subtype.ext hv
    have hpoint : v.val = x.val := congrArg (fun z : gammaGroundNativeProductDomain (Y (tag i)) (H (tag i)) => z.val) (ht (tag i) hv')
    exact hpoint ▸ v.property
  · rintro ⟨⟨i,he⟩,hx⟩
    subst j
    let v : (E i).source := ⟨x.val,hx⟩
    have hp : (E i).inclusion v = x := Subtype.ext (Prod.eta x.val)
    refine ⟨i,Finset.mem_univ i,v,?_⟩
    exact congrArg (fun z : gammaGroundNativeProductDomain (Y (tag i)) (H (tag i)) => (t (tag i) z).val) hp

theorem gammaGroundTensorBoxInParent_image
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (j : J) (i : {i // tag i = j}) :
    ((t j).comp (gammaGroundTensorBoxInParent Y H tag E j i).inclusion).image.carrier =
      ((t (tag i.val)).comp (E i.val).inclusion).image.carrier := by
  rcases i with ⟨i,he⟩
  subst j
  rfl

theorem gammaGroundTensorBox_children_disjoint
    (Y : J → GammaGroundRESUnitChart hc B r) (H : J → GammaGroundGammaPiece hc B m)
    (t : ∀ j, GammaGroundMap (gammaGroundNativeProductDomain (Y j) (H j)) U)
    (tag : ι → J) (E : ∀ i, GammaGroundTensorBox (Y (tag i)) (H (tag i)))
    (hd : ∀ i l, i ≠ l → Disjoint ((t (tag i)).comp (E i).inclusion).image.carrier
      ((t (tag l)).comp (E l).inclusion).image.carrier)
    (j : J) (i l : {i // tag i = j}) (hil : i ≠ l) :
    Disjoint (gammaGroundTensorBoxInParent Y H tag E j i).source.carrier
      (gammaGroundTensorBoxInParent Y H tag E j l).source.carrier := by
  let A := gammaGroundTensorBoxInParent Y H tag E j i
  let D := gammaGroundTensorBoxInParent Y H tag E j l
  have hd' : Disjoint ((t j).comp A.inclusion).image.carrier ((t j).comp D.inclusion).image.carrier := by
    rw [gammaGroundTensorBoxInParent_image,gammaGroundTensorBoxInParent_image]
    exact hd i.val l.val (fun he => hil (Subtype.ext he))
  apply Set.disjoint_left.mpr
  intro z hA hD
  let x : gammaGroundNativeProductDomain (Y j) (H j) := ⟨z,A.gamma_subset hA.1,A.residue_subset hA.2⟩
  have h1 : (t j x).val ∈ ((t j).comp A.inclusion).image.carrier :=
    ⟨⟨z,hA⟩,congrArg (fun w : gammaGroundNativeProductDomain (Y j) (H j) => (t j w).val)
      (show A.inclusion ⟨z,hA⟩ = x from Subtype.ext (Prod.eta z))⟩
  have h2 : (t j x).val ∈ ((t j).comp D.inclusion).image.carrier :=
    ⟨⟨z,hD⟩,congrArg (fun w : gammaGroundNativeProductDomain (Y j) (H j) => (t j w).val)
      (show D.inclusion ⟨z,hD⟩ = x from Subtype.ext (Prod.eta z))⟩
  exact Set.disjoint_left.mp hd' h1 h2
end DiamondIntegral.Section3
