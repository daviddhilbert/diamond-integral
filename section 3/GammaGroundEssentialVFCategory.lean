import «section 3».GammaGroundEssentialVFGerms
import Mathlib.CategoryTheory.Groupoid

/-! The quotient groupoid of essential Gamma-ground bijections. This is
the ambient essential groupoid; imposing volume preservation is separate. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {n r s : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

def GammaGroundEssentialGerm
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)) :=
  {e : GammaGroundGeneric A ≃ GammaGroundGeneric B //
    ∃ f : GammaGroundEssentialVFMap A B, f.genericEquiv hκ hs hS hv hn = e}

def gammaGroundEssentialOfRepresentative
    {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}
    (f : GammaGroundEssentialVFMap A B) : GammaGroundEssentialGerm hκ hs hS hv hn A B :=
  ⟨f.genericEquiv hκ hs hS hv hn, f, rfl⟩

def gammaGroundEssentialAESetoid
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)) : Setoid (GammaGroundEssentialVFMap A B) where
  r f g := f.genericEquiv hκ hs hS hv hn = g.genericEquiv hκ hs hS hv hn
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h j => h.trans j⟩

def gammaGroundEssentialQuotientEquiv
    (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)) :
    Quotient (gammaGroundEssentialAESetoid hκ hs hS hv hn A B) ≃ GammaGroundEssentialGerm hκ hs hS hv hn A B := by
  let F : Quotient (gammaGroundEssentialAESetoid hκ hs hS hv hn A B) → GammaGroundEssentialGerm hκ hs hS hv hn A B :=
    Quotient.lift (gammaGroundEssentialOfRepresentative hκ hs hS hv hn) (fun _ _ h => Subtype.ext h)
  apply Equiv.ofBijective F
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g he
    exact Quotient.sound (congrArg Subtype.val he)
  · rintro ⟨e, f, rfl⟩
    exact ⟨Quotient.mk _ f, rfl⟩

abbrev GammaGroundEssentialDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (n : ℕ) :=
  Σ r, GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)

def gammaGroundEssentialGroupoid : Groupoid (GammaGroundEssentialDomain hc ground n) where
  Hom A B := GammaGroundEssentialGerm hκ hs hS hv hn A.2 B.2
  id A := ⟨Equiv.refl _, ⟨GammaGroundEssentialVFMap.id A.2,
    GammaGroundEssentialVFMap.genericEquiv_id hκ hs hS hv hn⟩⟩
  comp {A B C} f g := ⟨f.val.trans g.val, by
    obtain ⟨p, hp⟩ := f.property
    obtain ⟨q, hq⟩ := g.property
    exact ⟨GammaGroundEssentialVFMap.comp hκ hs hS hv hn p q,
      (GammaGroundEssentialVFMap.genericEquiv_comp hκ hs hS hv hn p q).trans
        (congrArg₂ Equiv.trans hp hq)⟩⟩
  id_comp f := by apply Subtype.ext; exact Equiv.refl_trans f.val
  comp_id f := by apply Subtype.ext; exact Equiv.trans_refl f.val
  assoc f g h := by apply Subtype.ext; exact Equiv.trans_assoc f.val g.val h.val
  inv {A B} f := ⟨f.val.symm, by
    obtain ⟨p, hp⟩ := f.property
    exact ⟨p.symm, (GammaGroundEssentialVFMap.genericEquiv_symm hκ hs hS hv hn p).trans
      (congrArg Equiv.symm hp)⟩⟩
  inv_comp f := by apply Subtype.ext; exact Equiv.symm_trans_self f.val
  comp_inv f := by apply Subtype.ext; exact Equiv.self_trans_symm f.val

end DiamondIntegral.Section3
