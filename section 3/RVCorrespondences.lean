import «section 3».RVVolumeForms
import Section4.Products

set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

def RVObject.correspondence (U V : RVObject (M := M) S k) (F : U ⟶ V) :
    DefSet ((rawRVSpace (M := M) k).prod (rawRVSpace k)) S :=
  (U.volume.pair (V.volume.comp F.map)).image

theorem RVObject.correspondence_mem (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (r s : (rawRVSpace (M := M) k).Carrier) :
    (r, s) ∈ (U.correspondence V F).carrier ↔
      ∃ a : U.domain, (U.volume a).val = r ∧ (V.volume (F.map a)).val = s := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨a, hr, hs⟩
    exact ⟨a, Prod.ext hr hs⟩

theorem RVObject.correspondence_subset (U V : RVObject (M := M) S k) (F : U ⟶ V) :
    (U.correspondence V F).carrier ⊆ U.volume.image.carrier ×ˢ V.volume.image.carrier := by
  rintro ⟨r, s⟩ h
  obtain ⟨a, hr, hs⟩ := (U.correspondence_mem V F r s).mp h
  exact ⟨⟨a, hr⟩, ⟨F.map a, hs⟩⟩

theorem RVObject.correspondence_symm (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (r s : (rawRVSpace (M := M) k).Carrier) :
    (r, s) ∈ (U.correspondence V F).carrier ↔ (s, r) ∈ (V.correspondence U F.symm).carrier := by
  rw [U.correspondence_mem V F, V.correspondence_mem U F.symm]
  constructor
  · rintro ⟨a, hr, hs⟩
    refine ⟨F.map a, hs, ?_⟩
    rw [F.symm_apply_apply]
    exact hr
  · rintro ⟨b, hs, hr⟩
    refine ⟨F.symm.map b, hr, ?_⟩
    rw [F.apply_symm_apply]
    exact hs

theorem RVObject.correspondence_fibre_finite (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (r : (rawRVSpace (M := M) k).Carrier) :
    {s | (r, s) ∈ (U.correspondence V F).carrier}.Finite := by
  let t : DefSet.univ (rawRVSpace (M := M) k) S := ⟨r, Set.mem_univ _⟩
  apply ((U.finite t).image (fun a => (V.volume (F.map a)).val)).subset
  intro s hs
  obtain ⟨a, hr, hs⟩ := (U.correspondence_mem V F r s).mp hs
  exact ⟨a, Subtype.ext hr, hs⟩

theorem RVObject.correspondence_reverse_fibre_finite (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (s : (rawRVSpace (M := M) k).Carrier) :
    {r | (r, s) ∈ (U.correspondence V F).carrier}.Finite := by
  apply (V.correspondence_fibre_finite U F.symm s).subset
  intro r hr
  exact (U.correspondence_symm V F r s).mp hr

def RVObject.correspondenceFinitary (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (r : U.volume.image) : Set (rawRVSpace (M := M) k).Carrier :=
  {s | (r.val, s) ∈ (U.correspondence V F).carrier}

theorem RVObject.correspondenceFinitary_nonempty (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (r : U.volume.image) : (U.correspondenceFinitary V F r).Nonempty := by
  obtain ⟨a, ha⟩ := r.property
  exact ⟨(V.volume (F.map a)).val, (U.correspondence_mem V F _ _).mpr ⟨a, ha, rfl⟩⟩

theorem RVObject.correspondenceFinitary_finite (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (r : U.volume.image) : (U.correspondenceFinitary V F r).Finite := U.correspondence_fibre_finite V F r.val

theorem RVObject.correspondenceFinitary_subset (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (r : U.volume.image) : U.correspondenceFinitary V F r ⊆ V.volume.image.carrier := by
  intro s hs
  exact (U.correspondence_subset V F hs).2

def RVObject.targetOfImage (U : RVObject (M := M) S k) (r : U.volume.image) : Fin k → Section2.RV M :=
  fun i => ⟨r.val i, by
    obtain ⟨a, ha⟩ := r.property
    intro he
    apply U.nonzero a i
    exact (congrArg (fun t => (t i).val) ha).trans (congrArg Subtype.val he)⟩

def RVObject.correspondencePoint (U V : RVObject (M := M) S k) (F : U ⟶ V) (a : U.domain) :
    U.correspondence V F := ⟨((U.volume a).val, (V.volume (F.map a)).val), ⟨a, rfl⟩⟩

def RVObject.correspondenceJacobian (U V : RVObject (M := M) S k) (F : U ⟶ V)
    (p : U.correspondence V F) : Section2.Gamma M :=
  Section2.gammaJacobian
    (U.targetOfImage ⟨p.val.1, (U.correspondence_subset V F p.property).1⟩, Fin.elim0)
    (V.targetOfImage ⟨p.val.2, (U.correspondence_subset V F p.property).2⟩, Fin.elim0)

theorem RVObject.correspondenceJacobian_at (U V : RVObject (M := M) S k) (F : U ⟶ V) (a : U.domain) :
    U.correspondenceJacobian V F (U.correspondencePoint V F a) =
      Section2.gammaJacobian (U.target a, Fin.elim0) (V.target (F.map a), Fin.elim0) := rfl

end DiamondIntegral.Section3
