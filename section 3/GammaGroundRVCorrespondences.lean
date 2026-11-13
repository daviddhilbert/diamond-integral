import «section 3».GammaGroundMeasuredRVCategories
import «section 3».GammaGroundGammaCodeFormRestrictions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {k : ℕ}
@[simp] theorem GammaGroundBijection.apply_symm_apply
    {P Q : Space LRV M} {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}
    (f : GammaGroundBijection A B) (b : B) : f.map (f.symm.map b) = b :=
  f.map.apply_inverse f.bijective b

def GammaGroundRVObject.correspondence (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V) :
    GammaGroundDefSet hc ground ((rawRVSpace (M := M) k).prod (rawRVSpace k)) :=
  (U.volume.pair (V.volume.comp F.map)).image

theorem GammaGroundRVObject.correspondence_mem (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (r s : (rawRVSpace (M := M) k).Carrier) :
    (r, s) ∈ (U.correspondence V F).carrier ↔
      ∃ a : U.domain, (U.volume a).val = r ∧ (V.volume (F.map a)).val = s := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨a, hr, hs⟩
    exact ⟨a, Prod.ext hr hs⟩

theorem GammaGroundRVObject.correspondence_subset (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V) :
    (U.correspondence V F).carrier ⊆ U.volume.image.carrier ×ˢ V.volume.image.carrier := by
  rintro ⟨r, s⟩ h
  obtain ⟨a, hr, hs⟩ := (U.correspondence_mem V F r s).mp h
  exact ⟨⟨a, hr⟩, ⟨F.map a, hs⟩⟩

theorem GammaGroundRVObject.correspondence_symm (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (r s : (rawRVSpace (M := M) k).Carrier) :
    (r, s) ∈ (U.correspondence V F).carrier ↔ (s, r) ∈ (V.correspondence U F.symm).carrier := by
  rw [U.correspondence_mem V F, V.correspondence_mem U F.symm]
  constructor
  · rintro ⟨a, hr, hs⟩
    refine ⟨F.map a, hs, ?_⟩
    rw [GammaGroundBijection.symm_apply_apply F]
    exact hr
  · rintro ⟨b, hs, hr⟩
    refine ⟨F.symm.map b, hr, ?_⟩
    rw [GammaGroundBijection.apply_symm_apply F]
    exact hs

theorem GammaGroundRVObject.correspondence_fibre_finite (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (r : (rawRVSpace (M := M) k).Carrier) :
    {s | (r, s) ∈ (U.correspondence V F).carrier}.Finite := by
  let t : GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k) := ⟨r, Set.mem_univ _⟩
  apply ((U.finite t).image (fun a => (V.volume (F.map a)).val)).subset
  intro s hs
  obtain ⟨a, hr, hs⟩ := (U.correspondence_mem V F r s).mp hs
  exact ⟨a, Subtype.ext hr, hs⟩

theorem GammaGroundRVObject.correspondence_reverse_fibre_finite (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (s : (rawRVSpace (M := M) k).Carrier) :
    {r | (r, s) ∈ (U.correspondence V F).carrier}.Finite := by
  apply (V.correspondence_fibre_finite U F.symm s).subset
  intro r hr
  exact (U.correspondence_symm V F r s).mp hr

def GammaGroundRVObject.correspondenceFinitary (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (r : U.volume.image) : Set (rawRVSpace (M := M) k).Carrier :=
  {s | (r.val, s) ∈ (U.correspondence V F).carrier}

theorem GammaGroundRVObject.correspondenceFinitary_nonempty (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (r : U.volume.image) : (U.correspondenceFinitary V F r).Nonempty := by
  obtain ⟨a, ha⟩ := r.property
  exact ⟨(V.volume (F.map a)).val, (U.correspondence_mem V F _ _).mpr ⟨a, ha, rfl⟩⟩

theorem GammaGroundRVObject.correspondenceFinitary_finite (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (r : U.volume.image) : (U.correspondenceFinitary V F r).Finite := U.correspondence_fibre_finite V F r.val

theorem GammaGroundRVObject.correspondenceFinitary_subset (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (r : U.volume.image) : U.correspondenceFinitary V F r ⊆ V.volume.image.carrier := by
  intro s hs
  exact (U.correspondence_subset V F hs).2

def GammaGroundRVObject.targetOfImage (U : GammaGroundRVObject hc ground k) (r : U.volume.image) : Fin k → Section2.RV M :=
  fun i => ⟨r.val i, by
    obtain ⟨a, ha⟩ := r.property
    intro he
    apply U.nonzero a i
    exact (congrArg (fun t => (t i).val) ha).trans (congrArg Subtype.val he)⟩

def GammaGroundRVObject.correspondencePoint (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V) (a : U.domain) :
    U.correspondence V F := ⟨((U.volume a).val, (V.volume (F.map a)).val), ⟨a, rfl⟩⟩

def GammaGroundRVObject.correspondenceJacobian (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V)
    (p : U.correspondence V F) : Section2.Gamma M :=
  Section2.gammaJacobian
    (U.targetOfImage ⟨p.val.1, (U.correspondence_subset V F p.property).1⟩, Fin.elim0)
    (V.targetOfImage ⟨p.val.2, (U.correspondence_subset V F p.property).2⟩, Fin.elim0)

theorem GammaGroundRVObject.correspondenceJacobian_at (U V : GammaGroundRVObject hc ground k) (F : U ⟶ V) (a : U.domain) :
    U.correspondenceJacobian V F (U.correspondencePoint V F a) =
      Section2.gammaJacobian (U.target a, Fin.elim0) (V.target (F.map a), Fin.elim0) := rfl

end DiamondIntegral.Section3
