import «section 3».GammaGroundGenericMeasuredVF
import «section 3».GammaGroundPointwiseVFMeasure

/-! The measured essential groupoid uses actual pointwise preserving
representatives. Its equivalence with the generic presentation follows
from the same-ground cofull refinement theorem. -/
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
variable {n : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)

def GammaGroundMeasuredVFRepresentative (U V : GammaGroundMeasuredVFData hc ground n) :=
  {f : GammaGroundEssentialVFMap U.domain V.domain //
    f.Preserves Values.vfValueHom (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V)}

def GammaGroundMeasuredVFGerm (U V : GammaGroundMeasuredVFData hc ground n) :=
  {e : GammaGroundGeneric U.domain ≃ GammaGroundGeneric V.domain //
    ∃ f : GammaGroundMeasuredVFRepresentative U V, f.val.genericEquiv hκ hs hS hv hn = e}

def gammaGroundMeasuredOfRepresentative {U V : GammaGroundMeasuredVFData hc ground n}
    (f : GammaGroundMeasuredVFRepresentative U V) : GammaGroundMeasuredVFGerm hκ hs hS hv hn U V :=
  ⟨f.val.genericEquiv hκ hs hS hv hn, f, rfl⟩

def gammaGroundMeasuredAESetoid (U V : GammaGroundMeasuredVFData hc ground n) :
    Setoid (GammaGroundMeasuredVFRepresentative U V) where
  r f g := f.val.genericEquiv hκ hs hS hv hn = g.val.genericEquiv hκ hs hS hv hn
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h j => h.trans j⟩

theorem gammaGroundMeasuredAE_iff_agreement {U V : GammaGroundMeasuredVFData hc ground n}
    (f g : GammaGroundMeasuredVFRepresentative U V) :
    (gammaGroundMeasuredAESetoid hκ hs hS hv hn U V).r f g ↔
      ∃ E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n U.arity),
        Section2.vfDimension (U.domain.sdiff E).carrier < (n : WithBot ℕ) ∧
        ∀ x ∈ E.carrier, ∃ (p : f.val.source) (q : g.val.source),
          p.val = x ∧ q.val = x ∧ (f.val.map p).val = (g.val.map q).val :=
  GammaGroundEssentialVFMap.genericEquiv_eq_iff hκ hs hS hv hn f.val g.val

def gammaGroundMeasuredQuotientEquiv (U V : GammaGroundMeasuredVFData hc ground n) :
    Quotient (gammaGroundMeasuredAESetoid hκ hs hS hv hn U V) ≃ GammaGroundMeasuredVFGerm hκ hs hS hv hn U V := by
  let F : Quotient (gammaGroundMeasuredAESetoid hκ hs hS hv hn U V) → GammaGroundMeasuredVFGerm hκ hs hS hv hn U V :=
    Quotient.lift (gammaGroundMeasuredOfRepresentative hκ hs hS hv hn) (fun _ _ h => Subtype.ext h)
  apply Equiv.ofBijective F
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g he
    exact Quotient.sound (congrArg Subtype.val he)
  · rintro ⟨e, f, rfl⟩
    exact ⟨Quotient.mk _ f, rfl⟩

def gammaGroundMeasuredGermEquivGeneric [CharZero (Section2.VF M)]
    (U V : GammaGroundMeasuredVFData hc ground n) :
    GammaGroundMeasuredVFGerm hκ hs hS hv hn U V ≃ GammaGroundGenericMeasuredVFGerm hκ hs hS hv hn U V :=
  Equiv.subtypeEquivRight (fun e => by
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨f.val, f.property.toGeneric, hf⟩
    · rintro ⟨f, hf, he⟩
      obtain ⟨g, hg, hge⟩ := f.exists_pointwise_preserving hκ hs hS hv hn U.form V.form hf
      exact ⟨⟨g, hg⟩, hge.trans he⟩)

@[instance_reducible] def gammaGroundPositiveMeasuredVFGroupoid [CharZero (Section2.VF M)] :
    Groupoid (GammaGroundMeasuredVFData hc ground n) where
  Hom U V := GammaGroundMeasuredVFGerm hκ hs hS hv hn U V
  id U := ⟨Equiv.refl _, by
    let f := GammaGroundEssentialVFMap.id U.domain
    have hf := GammaGroundEssentialVFMap.preservesGeneric_id hκ hs hS hv Values.vfValueHom (gammaGroundMeasuredVFWeight U)
    obtain ⟨g, hg, hge⟩ := f.exists_pointwise_preserving hκ hs hS hv hn U.form U.form hf
    exact ⟨⟨g, hg⟩, hge.trans (GammaGroundEssentialVFMap.genericEquiv_id hκ hs hS hv hn)⟩⟩
  comp {U V W} f g := ⟨f.val.trans g.val, by
    obtain ⟨p, hp⟩ := f.property
    obtain ⟨q, hq⟩ := g.property
    let r := GammaGroundEssentialVFMap.comp hκ hs hS hv hn p.val q.val
    have hr := GammaGroundEssentialVFMap.preservesGeneric_comp hκ hs hS hv hn Values.vfValueHom
      (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V) (gammaGroundMeasuredVFWeight W)
      p.val q.val p.property.toGeneric q.property.toGeneric
    obtain ⟨r', hr', he⟩ := r.exists_pointwise_preserving hκ hs hS hv hn U.form W.form hr
    exact ⟨⟨r', hr'⟩, he.trans ((GammaGroundEssentialVFMap.genericEquiv_comp hκ hs hS hv hn p.val q.val).trans
      (congrArg₂ Equiv.trans hp hq))⟩⟩
  id_comp f := by apply Subtype.ext; exact Equiv.refl_trans f.val
  comp_id f := by apply Subtype.ext; exact Equiv.trans_refl f.val
  assoc f g h := by apply Subtype.ext; exact Equiv.trans_assoc f.val g.val h.val
  inv {U V} f := ⟨f.val.symm, by
    obtain ⟨p, hp⟩ := f.property
    have hr := GammaGroundEssentialVFMap.preservesGeneric_symm hκ hs hS hv Values.vfValueHom
      (gammaGroundMeasuredVFWeight U) (gammaGroundMeasuredVFWeight V) p.val p.property.toGeneric
    obtain ⟨r, hr', he⟩ := p.val.symm.exists_pointwise_preserving hκ hs hS hv hn V.form U.form hr
    exact ⟨⟨r, hr'⟩, he.trans ((GammaGroundEssentialVFMap.genericEquiv_symm hκ hs hS hv hn p.val).trans
      (congrArg Equiv.symm hp))⟩⟩
  inv_comp f := by apply Subtype.ext; exact Equiv.symm_trans_self f.val
  comp_inv f := by apply Subtype.ext; exact Equiv.self_trans_symm f.val

end DiamondIntegral.Section3
