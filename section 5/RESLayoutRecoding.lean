import «section 5».RESLayoutStabilization
import «section 5».RESCertificateRecoding

/-! Whole layout certificates preserve their actual formal identities,
all finite relation trees, and their total graph under row recoding. -/
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

def RESLayoutStabilizationSchema.recode (R : GammaParameterRecode B p q sp sq)
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) : RESLayoutStabilizationSchema (F.recode R) (G.recode R) where
  stabilizerArity := W.stabilizerArity
  stabilizer := W.stabilizer.recode R
  relations := W.relations.map (recodeRESCertificate R)
  sourceArity := W.sourceArity
  targetArity := W.targetArity
  source := W.source.recode R
  target := W.target.recode R
  source_formal := by
    rw [RESExpressionSchema.formalValue_recode, W.source_formal, map_add, map_add,
      ← W.stabilizer.formalValue_recode R, ← resCertificateRight_formal_recode R W.relations]
    rw [formalSchemaRecode, FreeCommRing.lift_of]
  target_formal := by
    rw [RESExpressionSchema.formalValue_recode, W.target_formal, map_add, map_add,
      ← W.stabilizer.formalValue_recode R, ← resCertificateLeft_formal_recode R W.relations]
    rw [formalSchemaRecode, FreeCommRing.lift_of]
  graph := R.relation W.graph

def RESLayoutStabilizationSchema.RowAgreement (R : GammaParameterRecode B p q sp sq)
    {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) (z : Fin p → M) (t : Fin q → M) : Prop :=
  R.DomainAgreement F.domain z t ∧ R.DomainAgreement G.domain z t ∧
    W.stabilizer.RowAgreement R z t ∧
    (∀ I ∈ W.relations, I.2.2.RowAgreement R z t) ∧
    W.source.RowAgreement R z t ∧ W.target.RowAgreement R z t ∧ R.RelationAgreement W.graph z t

theorem RESLayoutStabilizationSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) {F : RESSetSchema B p a sp} {G : RESSetSchema B p b sp}
    (W : RESLayoutStabilizationSchema F G) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hrow : W.RowAgreement R z t) : W.Valid hc z ↔ (W.recode R).Valid hc t := by
  obtain ⟨hF, hG, hC, hI, hS, hT, hH⟩ := hrow
  have hrelations : (∀ I ∈ W.relations, I.2.2.Valid hc z) ↔
      (∀ I ∈ (W.recode R).relations, I.2.2.Valid hc t) := by
    change _ ↔ ∀ I ∈ W.relations.map (recodeRESCertificate R), I.2.2.Valid hc t
    rw [List.forall_mem_map]
    exact forall_congr' (fun I => imp_congr_right (fun hi => I.2.2.recode_valid_iff hc R z t hz ht (hI I hi)))
  have hbij : bijectiveMapRowValid sp (fun _ : Fin W.targetArity => .rv)
      W.source.setSchema.domain.val W.target.setSchema.domain.val W.graph.val z ↔
    bijectiveMapRowValid sq (fun _ : Fin W.targetArity => .rv)
      (W.source.recode R).setSchema.domain.val (W.target.recode R).setSchema.domain.val (R.relation W.graph).val t := by
    constructor
    · exact bijectiveMapRowValid_of_rows ht (W.source.recode_row_iff R z t hS)
        (W.target.recode_row_iff R z t hT) hH
    · exact bijectiveMapRowValid_of_rows hz (fun x => (W.source.recode_row_iff R z t hS x).symm)
        (fun y => (W.target.recode_row_iff R z t hT y).symm) (fun x y => (hH x y).symm)
  exact and_congr (F.recode_valid_iff hc R z t hz ht hF)
    (and_congr (G.recode_valid_iff hc R z t hz ht hG)
      (and_congr (W.stabilizer.recode_valid_iff hc R z t hz ht hC)
        (and_congr hrelations (and_congr (W.source.recode_valid_iff hc R z t hz ht hS)
          (and_congr (W.target.recode_valid_iff hc R z t hz ht hT) hbij)))))

end DiamondIntegral.Section5
