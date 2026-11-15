import «section 5».RESExpressionRecoding
import «section 5».OriginalValidityFormulas

/-! A complete expression witness stores one full actual total-domain
bijection graph. Its first-order validity implies native equality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

structure RESExpressionBijectionSchema (E : RESExpressionSchema B p sp a) (F : RESExpressionSchema B p sp b) where
  graph : GammaRelationFormula B p a b sp

def RESExpressionBijectionSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    {E : RESExpressionSchema B p sp a} {F : RESExpressionSchema B p sp b}
    (H : RESExpressionBijectionSchema E F) (z : Fin p → M) : Prop :=
  E.Valid hc z ∧ F.Valid hc z ∧
    bijectiveMapRowValid sp (fun _ : Fin b => .rv) E.setSchema.domain.val F.setSchema.domain.val H.graph.val z

theorem RESExpressionBijectionSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {E : RESExpressionSchema B p sp a} {F : RESExpressionSchema B p sp b}
    (H : RESExpressionBijectionSchema E F) : DefinableOverBase B sp {z | H.Valid hc z} :=
  (E.valid_definable hc).inter ((F.valid_definable hc).inter
    (gamma_bijection_validity_definable sp (fun _ : Fin a => .rv) (fun _ : Fin b => .rv)
      E.setSchema.domain.property F.setSchema.domain.property H.graph.property))

theorem RESExpressionBijectionSchema.native_equality (hc : CanonicalStructure.IsCanonical (M := M))
    {E : RESExpressionSchema B p sp a} {F : RESExpressionSchema B p sp b}
    (H : RESExpressionBijectionSchema E F) (z : Fin p → M) (h : H.Valid hc z) :
    E.nativeValue hc z h.1 = F.nativeValue hc z h.2.1 := by
  let K : RESBijectionSchema E.setSchema F.setSchema := ⟨H.graph⟩
  have hK : K.Valid hc z := ⟨E.setSchema_valid hc z h.1, F.setSchema_valid hc z h.2.1, h.2.2⟩
  exact (E.nativeClass_eq hc z h.1).symm.trans
    ((K.native_equality hc z hK).trans (F.nativeClass_eq hc z h.2.1))

def RESExpressionBijectionSchema.recode (R : GammaParameterRecode B p q sp sq)
    {E : RESExpressionSchema B p sp a} {F : RESExpressionSchema B p sp b}
    (H : RESExpressionBijectionSchema E F) : RESExpressionBijectionSchema (E.recode R) (F.recode R) :=
  ⟨R.relation H.graph⟩

theorem RESExpressionBijectionSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq)
    {E : RESExpressionSchema B p sp a} {F : RESExpressionSchema B p sp b}
    (H : RESExpressionBijectionSchema E F) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hE : E.RowAgreement R z t) (hF : F.RowAgreement R z t)
    (hH : R.RelationAgreement H.graph z t) : H.Valid hc z ↔ (H.recode R).Valid hc t := by
  have he := E.recode_row_iff R z t hE
  have hf := F.recode_row_iff R z t hF
  constructor
  · rintro ⟨hev, hfv, hbij⟩
    exact ⟨(E.recode_valid_iff hc R z t hz ht hE).mp hev,
      (F.recode_valid_iff hc R z t hz ht hF).mp hfv,
      bijectiveMapRowValid_of_rows ht he hf hH hbij⟩
  · rintro ⟨hev, hfv, hbij⟩
    exact ⟨(E.recode_valid_iff hc R z t hz ht hE).mpr hev,
      (F.recode_valid_iff hc R z t hz ht hF).mpr hfv,
      bijectiveMapRowValid_of_rows hz (fun x => (he x).symm) (fun y => (hf y).symm)
        (fun x y => (hH x y).symm) hbij⟩

end DiamondIntegral.Section5
