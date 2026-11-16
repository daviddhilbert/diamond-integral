import «section 6».UnaryCoreCharts

/-! A whole affine core chart identifies the exact inverse image of a
new variable cutoff. This excludes accidental capture of another core.
The same chart survives regularization with all tags constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem unaryTaggedDisc_centre_mem (p : Mixed M 1 r) (γ : Gamma M) : p ∈ unaryTaggedDisc p γ := by
  refine ⟨rfl,?_⟩
  rw [sub_self]
  exact gamma_lt_value_zero γ

namespace UnaryCoreChart
variable {f : Map A B} {p : A} {γ : Gamma M}

theorem preimage_disc_exact (C : UnaryCoreChart f p γ) (hA : IsRVPullback A.carrier)
    (hp : p.val.1 0≠0) (hγ : vfValue (p.val.1 0) ≤ γ.val) (hf : Function.Injective f) (a : A) :
    (f a).val ∈ unaryTaggedDisc (f p).val γ ↔ a.val ∈ unaryTaggedDisc p.val γ := by
  constructor
  · intro ha
    have hImage : (f a).val ∈ C.image := (Set.ext_iff.mp (C.image_exact hA hp hγ) _).mpr ha
    obtain ⟨b,hb,hba⟩ := hImage
    have he : b=a := hf (Subtype.ext hba)
    exact he ▸ hb
  · intro ha
    exact (Set.ext_iff.mp (C.image_exact hA hp hγ) _).mp ⟨a,ha,rfl⟩

theorem capture_exact (C : UnaryCoreChart f p γ) (hA : IsRVPullback A.carrier)
    (hp : p.val.1 0≠0) (hγ : vfValue (p.val.1 0) ≤ γ.val) (hf : Function.Injective f)
    (D : UnaryRelativeApertureData B)
    (hu : (f p).val.2 ∈ D.focusData.activeTags.carrier)
    (hFocus : D.focusData.focus (f p).val.2=(f p).val.1 0)
    (hEndpoint : vfValue (D.endpoint (f p).val.2)=γ.val) (a : A) :
    ((f a).val.2=(f p).val.2 ∧ D.core (f a).val=true) ↔ a.val ∈ unaryTaggedDisc p.val γ := by
  rw [← C.preimage_disc_exact hA hp hγ hf a]
  constructor
  · rintro ⟨hTags,hCore⟩
    have huA : (f a).val.2 ∈ D.focusData.activeTags.carrier := hTags.symm ▸ hu
    rw [D.core_active ⟨(f a).val,(f a).property,huA⟩] at hCore
    have h : vfValue (D.endpoint (f a).val.2)<
        vfValue ((f a).val.1 0-D.focusData.focus (f a).val.2) := of_decide_eq_true hCore
    rw [hTags,hFocus,hEndpoint] at h
    exact ⟨hTags,h⟩
  · rintro ⟨hTags,hClose⟩
    refine ⟨hTags,?_⟩
    have huA : (f a).val.2 ∈ D.focusData.activeTags.carrier := hTags.symm ▸ hu
    rw [D.core_active ⟨(f a).val,(f a).property,huA⟩]
    apply decide_eq_true
    change vfValue (D.endpoint (f a).val.2)<vfValue ((f a).val.1 0-D.focusData.focus (f a).val.2)
    rw [hTags,hFocus,hEndpoint]
    exact hClose

theorem afterRegularization (C : UnaryCoreChart f p γ)
    (hBound : vfValue ((f p).val.1 0) ≤ γ.val) :
    UnaryCoreChart ((regularization B).comp f) p γ := by
  have hNZ : (f p).val.1 0≠0 := by
    intro hz
    have h := hBound
    rw [hz,value_zero] at h
    exact γ.property (le_antisymm (Values.le_infinity _) h)
  refine ⟨C.field,?_⟩
  intro a hTags hClose
  have hRV : rv M ((f a).val.1 0)=rv M ((f p).val.1 0) := by
    apply (rv_eq_iff_value_close hNZ).mpr
    rw [C.field a hTags hClose,add_sub_cancel_right]
    exact hBound.trans_lt hClose
  have hVF : tupleRV M (f a).val.1=tupleRV M (f p).val.1 := by
    funext i
    fin_cases i
    exact hRV
  change Fin.append (tupleRV M (f a).val.1) (f a).val.2=
    Fin.append (tupleRV M (f p).val.1) (f p).val.2
  rw [hVF,C.tags a hTags hClose]

end UnaryCoreChart
end DiamondIntegral.Section6
