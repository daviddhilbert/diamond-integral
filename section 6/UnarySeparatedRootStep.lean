import «section 6».UnaryRootFieldValues
import «section 6».UnaryFocusRadiusFloor
import «section 6».UnaryRootStep

/-! A finite-aperture root step whose core contains at most one root
on each retained RV label. The coefficient is chosen over the original
base, using all nonzero differences in the finite center family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRootFamily
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_separated_root_step (R : UnaryRootFamily A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    ∃ D : CentripetalData (G := G) A,D.coordinate=0 ∧ D.activeTags=R.activeTags ∧
      (∀ x u,D.focus x u=Barycentre.mean (R.fibre u)) ∧
      ∀ p : A,p.val ∈ R.roots.carrier → D.core p.val=true →
        p.val.1 0=Barycentre.mean (R.fibre p.val.2) := by
  obtain ⟨F,hFact,hFfocus⟩ := R.exists_focusData h00 hc hs hsmall hA hD htag
  let E := R.fieldValues ∪ scalarFocusImage F.focusMap
  have hE : E.Finite := (R.fieldValues_finite hc hs hsmall).union (F.focusImage_finite hc hs hsmall)
  have hEdef : S.Definable₁ LRV (Subtype.val '' E) := by
    rw [show Subtype.val '' E=Subtype.val '' R.fieldValues ∪ Subtype.val '' scalarFocusImage F.focusMap
      from Set.image_union _ _ _]
    exact R.fieldValues_definable.union (scalarFocusImage_definable F.focusMap)
  obtain ⟨d,hd,hdDef,hdPos,hdBound⟩ := exists_named_vf_above_finite_family h00 hc hv V hV hVS hSV hnt
    (finiteCenterDifferences E) (finiteCenterDifferences_definable E hEdef)
    (finiteCenterDifferences_finite E hE) (finiteCenterDifferences_nonzero E)
  obtain ⟨D,hcoord,hact,hfocus,hmap,hfloor⟩ := F.exists_centripetal_data_above_radius
    (finiteValue d hd) (finiteValue_named d hd hdDef) h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
  refine ⟨D,hcoord,hact.trans hFact,(fun x u => (hfocus x u).trans (hFfocus u)),fun p hp hcore => ?_⟩
  have hactive : p.val.2 ∈ F.activeTags.carrier := hFact.symm ▸ R.root_active hp
  have hfmem : F.focus p.val.2 ∈ scalarFocusImage F.focusMap :=
    ⟨⟨p.val,p.property,hactive⟩,F.focusMap_eq _⟩
  have hroot : p.val.1 0 ∈ R.fieldValues := ⟨⟨p.val,hp⟩,rfl⟩
  have hext : D.extendedFocus p.val=F.focus p.val.2 := by
    rw [D.extendedFocus_active p.property (hact.symm ▸ hactive),hfocus]
  have hclose : vfValue (D.coefficient*F.focus p.val.2) < vfValue (p.val.1 0-F.focus p.val.2) := by
    have hh := of_decide_eq_true hcore
    simpa only [hcoord,hext] using hh
  have hrootFocus : p.val.1 0=F.focus p.val.2 := by
    by_contra hn
    have hh := hdBound (p.val.1 0-F.focus p.val.2)
      ⟨p.val.1 0,Or.inl hroot,F.focus p.val.2,Or.inr hfmem,hn,rfl⟩
    exact lt_irrefl _ (hh.trans ((hfloor _ hfmem).trans hclose))
  exact hrootFocus.trans (hFfocus p.val.2)

end DiamondIntegral.Section6.UnaryRootFamily
