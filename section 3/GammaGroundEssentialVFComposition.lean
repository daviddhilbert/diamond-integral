import «section 3».GammaGroundEssentialVFMap

/-! Essential representatives compose using the actual overlap of their
middle domains. Cofullness is proved from the original-field generic
criterion, with no descent of an arbitrary real-code definable cut. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3.GammaGroundEssentialVFMap
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {n r s t : ℕ}
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
variable {C : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n t)}

def compSource (f : GammaGroundEssentialVFMap A B) (g : GammaGroundEssentialVFMap B C) := f.map.preimage g.source

theorem compSource_subset (f : GammaGroundEssentialVFMap A B) (g : GammaGroundEssentialVFMap B C) :
    (f.compSource g).carrier ⊆ f.source.carrier := f.map.preimage_subset g.source

def compMiddle (f : GammaGroundEssentialVFMap A B) (g : GammaGroundEssentialVFMap B C) :
    GammaGroundMap (f.compSource g) g.source :=
  (f.map.restrict (f.compSource_subset g)).corestrict (by
    rintro ⟨x, p, rfl, hp⟩
    exact hp)

theorem compMiddle_injective (f : GammaGroundEssentialVFMap A B) (g : GammaGroundEssentialVFMap B C) :
    Function.Injective (f.compMiddle g) := by
  intro a b he
  apply Subtype.ext
  have h : f.map ⟨a.val, f.compSource_subset g a.property⟩ =
      f.map ⟨b.val, f.compSource_subset g b.property⟩ := Subtype.ext (congrArg (fun x : g.source => x.val) he)
  exact congrArg (fun x : f.source => x.val) (f.bijective.injective h)

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

include hκ hs hS hv hn in
theorem generic_mem_compSource (f : GammaGroundEssentialVFMap A B) (g : GammaGroundEssentialVFMap B C)
    (a : GammaGroundGeneric A) : a.val.val ∈ (f.compSource g).carrier := by
  let p : f.source := ⟨a.val.val,
    gammaGround_mem_of_small_complement f.source hκ hs hS hv hn f.source_small a⟩
  have hb := gammaGround_mem_of_small_complement g.source hκ hs hS hv hn g.source_small
    (f.genericFun hκ hs hS hv hn a)
  exact ⟨p, rfl, hb⟩

def comp (f : GammaGroundEssentialVFMap A B) (g : GammaGroundEssentialVFMap B C) : GammaGroundEssentialVFMap A C := by
  let E := f.compSource g
  let F := g.map.comp (f.compMiddle g)
  have hF : Function.Injective F := g.bijective.injective.comp (f.compMiddle_injective g)
  have hsrc : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ) :=
    gammaGround_small_complement_of_generic A E hκ hs hS hv hn (f.generic_mem_compSource hκ hs hS hv hn g)
  have htar : Section2.vfDimension (C.sdiff F.image).carrier < (n : WithBot ℕ) := by
    apply gammaGround_small_complement_of_generic C F.image hκ hs hS hv hn
    intro c
    obtain ⟨a, ha⟩ := ((f.genericEquiv hκ hs hS hv hn).trans (g.genericEquiv hκ hs hS hv hn)).surjective c
    let p : E := ⟨a.val.val, f.generic_mem_compSource hκ hs hS hv hn g a⟩
    exact ⟨p, congrArg (fun z : GammaGroundGeneric C => z.val.val) ha⟩
  exact ⟨E, F.image, (f.compSource_subset g).trans f.source_subset,
    by rintro y ⟨p, rfl⟩; exact g.target_subset (F p).property,
    hsrc, htar, F.toImage, F.toImage_bijective hF⟩

theorem genericEquiv_comp (f : GammaGroundEssentialVFMap A B) (g : GammaGroundEssentialVFMap B C) :
    (comp hκ hs hS hv hn f g).genericEquiv hκ hs hS hv hn =
      (f.genericEquiv hκ hs hS hv hn).trans (g.genericEquiv hκ hs hS hv hn) := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  apply Subtype.ext
  rfl

end DiamondIntegral.Section3.GammaGroundEssentialVFMap
