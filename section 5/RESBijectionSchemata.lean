import «section 5».RESValueBoundDefinability
import «section 5».RESSetSchemaRecoding
import «section 5».OriginalValidityFormulas
import IntegrationSection6.GammaFamilyBijectionValidity
import IntegrationSection6.GammaMapRowTransport

/-! Full native RES bijection witnesses have original-base first-order
validity loci. Exact domain and graph rows transport the entire witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

structure RESBijectionSchema (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp) where
  graph : GammaRelationFormula B p a b sp

def RESBijectionSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (H : RESBijectionSchema F G) (z : Fin p → M) : Prop :=
  F.Valid hc z ∧ G.Valid hc z ∧
    bijectiveMapRowValid sp (fun _ : Fin b => .rv) F.domain.val G.domain.val H.graph.val z

theorem RESBijectionSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp} (H : RESBijectionSchema F G) :
    DefinableOverBase B sp {z | H.Valid hc z} := by
  exact (F.valid_definable hc).inter ((G.valid_definable hc).inter
    (gamma_bijection_validity_definable sp (fun _ : Fin a => .rv) (fun _ : Fin b => .rv)
      F.domain.property G.domain.property H.graph.property))

theorem RESBijectionSchema.validity_formula (hc : CanonicalStructure.IsCanonical (M := M))
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp} (H : RESBijectionSchema F G) :
    ∃ φ : LRV.Formula (commonRealNames B ⊕ Fin p),
      ∀ z, φ.Realize (predicateParameterValues B z) ↔ H.Valid hc z :=
  original_validity_formula hc B sp {z | H.Valid hc z} (H.valid_definable hc)

def RESBijectionSchema.recode (R : GammaParameterRecode B p q sp sq)
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp} (H : RESBijectionSchema F G) :
    RESBijectionSchema (F.recode R) (G.recode R) := ⟨R.relation H.graph⟩

theorem RESBijectionSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (H : RESBijectionSchema F G) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hF : R.DomainAgreement F.domain z t) (hG : R.DomainAgreement G.domain z t)
    (hH : R.RelationAgreement H.graph z t) : H.Valid hc z ↔ (H.recode R).Valid hc t := by
  constructor
  · rintro ⟨hsource, htarget, hbij⟩
    exact ⟨(F.recode_valid_iff hc R z t hz ht hF).mp hsource,
      (G.recode_valid_iff hc R z t hz ht hG).mp htarget,
      bijectiveMapRowValid_of_rows ht hF hG hH hbij⟩
  · rintro ⟨hsource, htarget, hbij⟩
    exact ⟨(F.recode_valid_iff hc R z t hz ht hF).mpr hsource,
      (G.recode_valid_iff hc R z t hz ht hG).mpr htarget,
      bijectiveMapRowValid_of_rows hz (fun x => (hF x).symm) (fun y => (hG y).symm)
        (fun x y => (hH x y).symm) hbij⟩

end DiamondIntegral.Section5
