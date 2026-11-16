import «section 6».ApertureRelease

/-! The retained finite-aperture core is a full RV disc after translation.
Membership in every invariant partition piece factors through the focus
base. Together with the released-annulus formula this checks both new
branches of an aperture replacement as equalities of full sets. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {X : Type*}

theorem rv_eq_iff_value_close {a b : VF M} (hb : b ≠ 0) :
    rv M a = rv M b ↔ vfValue b < vfValue (a-b) := by
  constructor
  · intro he
    have he' : iRv a.val = iRv b.val := congrArg Subtype.val he
    rw [CanonicalRV.encoded_eq_iff_close a.property b.property
      (fun h => hb (Subtype.ext h))] at he'
    change ¬ VFValued.predV b (a-b) at he'
    rw [Values.vf_pred_iff_gamma_le,not_le] at he'
    exact he'
  · exact rv_eq_of_value_close hb

def CorePiece (A : Set (VF M × X)) (focus center : X → VF M) : Set (VF M × X) :=
  {p | vfValue (center p.2) < vfValue p.1 ∧ (focus p.2+p.1,p.2) ∈ A}

def coreTranslate (center : X → VF M) (p : VF M × X) : VF M × X :=
  (p.1+center p.2,p.2)

theorem corePiece_factorization (A : Set (VF M × X))
    (focus center : X → VF M) (α : X → Gamma M)
    (hα : ∀ x, (α x).val ≤ vfValue (center x))
    (hA : ∀ x a b, (α x).val < vfValue (a-b) → ((a,x) ∈ A ↔ (b,x) ∈ A)) :
    CorePiece A focus center =
      {p | vfValue (center p.2) < vfValue p.1} ∩ Prod.snd ⁻¹' FocusBase A focus := by
  ext p
  change (vfValue (center p.2) < vfValue p.1 ∧ (focus p.2+p.1,p.2) ∈ A) ↔
    vfValue (center p.2) < vfValue p.1 ∧ (focus p.2,p.2) ∈ A
  have hd (hp : vfValue (center p.2) < vfValue p.1) :
      (α p.2).val < vfValue ((focus p.2+p.1)-focus p.2) := by
    simpa only [add_sub_cancel_left] using (hα p.2).trans_lt hp
  exact ⟨fun ⟨hp,ha⟩ => ⟨hp,(hA p.2 _ _ (hd hp)).mp ha⟩,
    fun ⟨hp,ha⟩ => ⟨hp,(hA p.2 _ _ (hd hp)).mpr ha⟩⟩

theorem coreTranslate_image_exact (A : Set (VF M × X))
    (focus center : X → VF M) (α : X → Gamma M)
    (hc : ∀ x, center x ≠ 0) (hα : ∀ x, (α x).val ≤ vfValue (center x))
    (hA : ∀ x a b, (α x).val < vfValue (a-b) → ((a,x) ∈ A ↔ (b,x) ∈ A)) :
    coreTranslate center '' CorePiece A focus center =
      {p | rv M p.1 = rv M (center p.2) ∧ (focus p.2,p.2) ∈ A} := by
  rw [corePiece_factorization A focus center α hα hA]
  ext p
  constructor
  · rintro ⟨⟨d,x⟩,⟨hd,hmem⟩,rfl⟩
    refine ⟨(rv_eq_iff_value_close (hc x)).mpr ?_,hmem⟩
    simpa only [coreTranslate,add_sub_cancel_right] using
      (show vfValue (center x) < vfValue d from hd)
  · rintro ⟨hrv,hmem⟩
    refine ⟨(p.1-center p.2,p.2),⟨(rv_eq_iff_value_close (hc p.2)).mp hrv,hmem⟩,?_⟩
    exact Prod.ext (sub_add_cancel _ _) rfl

theorem coreTranslate_image_rv_saturated (A : Set (VF M × X))
    (focus center : X → VF M) (α : X → Gamma M)
    (hc : ∀ x, center x ≠ 0) (hα : ∀ x, (α x).val ≤ vfValue (center x))
    (hA : ∀ x a b, (α x).val < vfValue (a-b) → ((a,x) ∈ A ↔ (b,x) ∈ A))
    (x : X) (a b : VF M) (hrv : rv M a = rv M b) :
    (a,x) ∈ coreTranslate center '' CorePiece A focus center ↔
      (b,x) ∈ coreTranslate center '' CorePiece A focus center := by
  rw [coreTranslate_image_exact A focus center α hc hα hA]
  change (rv M a = rv M (center x) ∧ (focus x,x) ∈ A) ↔
    rv M b = rv M (center x) ∧ (focus x,x) ∈ A
  rw [hrv]

end DiamondIntegral.Section6
