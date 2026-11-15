import «section 5».OriginalDomainProducts
import «section 5».RESBijectionSchemata
import «section 5».OriginalEulerRowValues
import «section 5».OriginalEulerRecoding

/-! One finite original-base RV rectangle witness retains its source,
RES factor, full Gamma support, Euler certificate and complete map graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

structure RVRectanglePieceSchema (B : Base (M := M)) (p a : ℕ) (sp : Fin p → SortTag) where
  source : GammaDomainFormula B p a sp
  residueArity : ℕ
  freeArity : ℕ
  residue : RESSetSchema B p residueArity sp
  gamma : GammaDomainFormula B p freeArity sp
  euler : OriginalEulerCertificate B sp freeArity
  graph : GammaRelationFormula B p a (residueArity+freeArity) sp

def RVRectanglePieceSchema.target (F : RVRectanglePieceSchema B p a sp) :=
  originalDomainProduct F.residue.domain F.gamma

def RVRectanglePieceSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RVRectanglePieceSchema B p a sp) (z : Fin p → M) : Prop :=
  F.residue.Valid hc z ∧ F.euler.ValidFor hc F.gamma z ∧
    bijectiveMapRowValid sp (fun _ : Fin (F.residueArity+F.freeArity) => .rv)
      F.source.val F.target.val F.graph.val z

theorem RVRectanglePieceSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (F : RVRectanglePieceSchema B p a sp) : DefinableOverBase B sp {z | F.Valid hc z} := by
  have hb := gamma_bijection_validity_definable sp (fun _ : Fin a => .rv)
    (fun _ : Fin (F.residueArity+F.freeArity) => .rv) F.source.property F.target.property F.graph.property
  have h := (F.residue.valid_definable hc).inter ((F.euler.validFor_definable hc F.gamma).inter hb)
  convert h using 1
  ext z
  change (_ ∧ _ ∧ _) ↔ (_ ∧ (_ ∧ _) ∧ _)
  exact ⟨fun h => ⟨h.1,⟨h.1.1,h.2.1⟩,h.2.2⟩,fun h => ⟨h.1,h.2.1.2,h.2.2⟩⟩

def RVRectanglePieceSchema.recode (R : GammaParameterRecode B p q sp sq)
    (F : RVRectanglePieceSchema B p a sp) : RVRectanglePieceSchema B q a sq where
  source := R.domain F.source
  residueArity := F.residueArity
  freeArity := F.freeArity
  residue := F.residue.recode R
  gamma := R.domain F.gamma
  euler := F.euler.recode R
  graph := R.relation F.graph

def RVRectanglePieceSchema.RowAgreement (R : GammaParameterRecode B p q sp sq)
    (F : RVRectanglePieceSchema B p a sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  R.DomainAgreement F.source z t ∧ R.DomainAgreement F.residue.domain z t ∧
    R.DomainAgreement F.gamma z t ∧ F.euler.RowAgreement R z t ∧ R.RelationAgreement F.graph z t

theorem RVRectanglePieceSchema.target_row_agreement (R : GammaParameterRecode B p q sp sq)
    (F : RVRectanglePieceSchema B p a sp) (z : Fin p → M) (t : Fin q → M)
    (hR : R.DomainAgreement F.residue.domain z t) (hG : R.DomainAgreement F.gamma z t)
    (w : Fin (F.residueArity+F.freeArity) → M) :
    Fin.append z w ∈ F.target.val ↔ Fin.append t w ∈ (F.recode R).target.val := by
  exact (originalDomainProduct_row F.residue.domain F.gamma z w).trans
    ((and_congr (hR _) (hG _)).trans
      (originalDomainProduct_row (R.domain F.residue.domain) (R.domain F.gamma) t w).symm)

theorem RVRectanglePieceSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (F : RVRectanglePieceSchema B p a sp)
    (z : Fin p → M) (t : Fin q → M) (hz : ∀ i, sortEval (sp i) (z i))
    (ht : ∀ i, sortEval (sq i) (t i)) (h : F.RowAgreement R z t) :
    F.Valid hc z ↔ (F.recode R).Valid hc t := by
  have hres := F.residue.recode_valid_iff hc R z t hz ht h.2.1
  have heu := F.euler.recode_validity_iff hc R F.gamma z t h.2.2.2.1 h.2.2.1
    (nativeGammaRelationSyntax hc).proper (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
  constructor
  · rintro ⟨hr,he,hb⟩
    exact ⟨hres.mp hr,heu.mp he,
      bijectiveMapRowValid_of_rows ht h.1 (F.target_row_agreement R z t h.2.1 h.2.2.1) h.2.2.2.2 hb⟩
  · rintro ⟨hr,he,hb⟩
    exact ⟨hres.mpr hr,heu.mpr he,
      bijectiveMapRowValid_of_rows hz (fun x => (h.1 x).symm)
        (fun w => (F.target_row_agreement R z t h.2.1 h.2.2.1 w).symm)
        (fun x y => (h.2.2.2.2 x y).symm) hb⟩

end DiamondIntegral.Section5
