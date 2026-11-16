import «section 6».OrdinarySmallDiscImages
import Section5.TransformGeometry

/-! Unary ordinary chains are locally translations on each original
RV fibre. At zero this uses the checked whole zero-disc formula; away
from zero each primitive retains locally constant RV labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}

def ordinaryUnaryField {r : ℕ} (p : Mixed M 1 r) : VF M := p.1 0

theorem ordinary_primitive_labels_of_sameRV
    (step : SpecialTransformations.Section5.Primitive R 1 A B) (p x : A)
    (hVF : tupleRV M x.val.1=tupleRV M p.val.1) (hRV : x.val.2=p.val.2) :
    (step.toMap x).val.2=(step.toMap p).val.2 := by
  cases step with
  | canonical A =>
      change Fin.append (tupleRV M x.val.1) x.val.2=Fin.append (tupleRV M p.val.1) p.val.2
      rw [hVF,hRV]
  | centripetal D =>
      change (D.toFocusGeometry.eta x.val).2=(D.toFocusGeometry.eta p.val).2
      simpa only [SpecialTransformations.Section5.FocusGeometry.eta_labels] using hRV

theorem ordinary_chain_locally_translation
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    ∀ p : A,∃ η : Gamma M,1 ≤ η ∧ ∀ x : A,x.val.2=p.val.2 →
      η.val < vfValue (ordinaryUnaryField x.val-ordinaryUnaryField p.val) →
      ordinaryUnaryField (T.toMap x).val-ordinaryUnaryField (T.toMap p).val=ordinaryUnaryField x.val-ordinaryUnaryField p.val := by
  induction T with
  | nil A => exact fun p => ⟨1,le_rfl,fun _ _ _ => rfl⟩
  | @cons a b c A B C step tail ih =>
    intro p
    by_cases hp0 : p.val.1 0=(0 : VF M)
    · obtain ⟨η,hη1,hFormula⟩ := ordinary_chain_whole_zero_disc_formula hc hs hsmall (.cons step tail) hT
      refine ⟨η,hη1,fun x hxTags hClose => ?_⟩
      have hpSmall : η.val < vfValue (p.val.1 0) := by rw [hp0]; exact gamma_lt_value_zero η
      have hxSmall : η.val < vfValue (x.val.1 0) := by simpa only [ordinaryUnaryField,hp0,sub_zero] using hClose
      exact congrArg₂ (fun a b : VF M => a-b)
        (congrFun (hFormula x hxSmall).1 0) (congrFun (hFormula p hpSmall).1 0)
    · obtain ⟨ηTail,hηTail1,hTail⟩ := ih hT.2 (step.toMap p)
      let η := max ηTail (finiteValue (ordinaryUnaryField p.val) hp0)
      refine ⟨η,hηTail1.trans (le_max_left _ _),fun x hxTags hClose => ?_⟩
      have hxRV : rv M (x.val.1 0)=rv M (p.val.1 0) :=
        (rv_eq_iff_value_close hp0).mpr ((show vfValue (p.val.1 0) ≤ η.val from le_max_right _ _).trans_lt hClose)
      have hVF : tupleRV M x.val.1=tupleRV M p.val.1 := by
        funext i
        fin_cases i
        exact hxRV
      have hStepTags := ordinary_primitive_labels_of_sameRV step p x hVF hxTags
      have hDifference : ordinaryUnaryField (step.toMap x).val-ordinaryUnaryField (step.toMap p).val=
          ordinaryUnaryField x.val-ordinaryUnaryField p.val := by
        simpa only [ordinaryUnaryField,SpecialTransformations.Section5.vfAt] using step.unary_sub x p hStepTags
      have hTailClose : ηTail.val < vfValue (ordinaryUnaryField (step.toMap x).val-ordinaryUnaryField (step.toMap p).val) := by
        rw [hDifference]
        exact (show ηTail.val ≤ η.val from le_max_left _ _).trans_lt hClose
      exact (hTail (step.toMap x) hStepTags hTailClose).trans hDifference

end DiamondIntegral.Section6
