import «section 3».GammaMeasuredIsomorphismSchemata
import «section 3».GammaMeasuredRowAgreements
import «section 3».GammaMeasuredEssentialSchemata
import IntegrationSection6.GammaAdmissibilitySchemata

/-! Finite geometric proof schemata use the existing domain, volume,
chart, coproduct, elementary, and row-agreement formulas. Only density
functionality is interpreted in the Gamma quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaMeasuredRVSchema.withBound (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (N : ℕ) :
    GammaMeasuredRVSchema hc B p a (k+1) sp :=
  .ofRVTemplate (F.toRVTemplate.withBound N)

inductive GammaMeasuredRelationSchema :
    {a b : ℕ} → GammaMeasuredRVSchema hc B p a (k+1) sp →
      GammaMeasuredRVSchema hc B p b (k+1) sp → Type
  | iso {a b : ℕ} (I : GammaMeasuredRVIsoSchema hc B p a b k sp) :
      GammaMeasuredRelationSchema I.source I.target
  | agreement {a : ℕ} (F G : GammaMeasuredRVSchema hc B p a (k+1) sp) :
      GammaMeasuredRelationSchema F G
  | elementary {a : ℕ} (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (N A : ℕ) :
      GammaMeasuredRelationSchema F (F.elementaryFormula.essential.withBound N)
  | symm {a b : ℕ} {F : GammaMeasuredRVSchema hc B p a (k+1) sp}
      {G : GammaMeasuredRVSchema hc B p b (k+1) sp} (H : GammaMeasuredRelationSchema F G) :
      GammaMeasuredRelationSchema G F
  | trans {a b c : ℕ} {F : GammaMeasuredRVSchema hc B p a (k+1) sp}
      {G : GammaMeasuredRVSchema hc B p b (k+1) sp}
      (E : GammaMeasuredRVSchema hc B p c (k+1) sp)
      (H : GammaMeasuredRelationSchema F E) (K : GammaMeasuredRelationSchema E G) :
      GammaMeasuredRelationSchema F G
  | coprod {a b c d : ℕ} {F : GammaMeasuredRVSchema hc B p a (k+1) sp}
      {G : GammaMeasuredRVSchema hc B p b (k+1) sp}
      {E : GammaMeasuredRVSchema hc B p c (k+1) sp}
      {D : GammaMeasuredRVSchema hc B p d (k+1) sp}
      (H : GammaMeasuredRelationSchema F G) (K : GammaMeasuredRelationSchema E D) (N L : ℕ) :
      GammaMeasuredRelationSchema ((F.coprodFormula E).withBound N) ((G.coprodFormula D).withBound L)

def GammaMeasuredRelationSchema.valid :
    {a b : ℕ} → {F : GammaMeasuredRVSchema hc B p a (k+1) sp} →
      {G : GammaMeasuredRVSchema hc B p b (k+1) sp} →
      GammaMeasuredRelationSchema F G → (Fin p → M) → Prop
  | _,_,_,_,.iso I,z => I.valid z
  | _,_,_,_,.agreement F G,z => F.valid z ∧ G.valid z ∧ F.toRVTemplate.sameRow G.toRVTemplate z
  | _,_,_,_,.elementary F N A,z => F.valid z ∧ (F.elementaryFormula.essential.withBound N).valid z ∧
      (GammaFiniteAdmissibilitySchema.mk F.object (Fin.last k) A).valid z
  | _,_,_,_,.symm H,z => H.valid z
  | _,_,_,_,.trans _ H K,z => H.valid z ∧ K.valid z
  | _,_,_,_,.coprod (F := F) (G := G) (E := E) (D := D) H K N L,z =>
      H.valid z ∧ K.valid z ∧ ((F.coprodFormula E).withBound N).valid z ∧
        ((G.coprodFormula D).withBound L).valid z

theorem GammaMeasuredRelationSchema.valid_definable
    {F : GammaMeasuredRVSchema hc B p a (k+1) sp} {G : GammaMeasuredRVSchema hc B p b (k+1) sp}
    (H : GammaMeasuredRelationSchema F G) : DefinableOverBase B sp {z | H.valid z} := by
  induction H with
  | iso I => exact I.valid_definable
  | agreement F G => exact F.valid_definable.inter (G.valid_definable.inter (F.toRVTemplate.sameRow_definable G.toRVTemplate))
  | elementary F N A =>
      exact F.valid_definable.inter ((F.elementaryFormula.essential.withBound N).valid_definable.inter
        (GammaFiniteAdmissibilitySchema.mk F.object (Fin.last k) A).valid_definable)
  | symm H ih => exact ih
  | trans E H K ihH ihK => exact ihH.inter ihK
  | @coprod a b c d F G E D H K N L ihH ihK =>
      exact ihH.inter (ihK.inter (((F.coprodFormula E).withBound N).valid_definable.inter
        ((G.coprodFormula D).withBound L).valid_definable))

end DiamondIntegral.Section3
