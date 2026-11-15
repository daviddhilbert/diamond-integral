import «section 5».RVRectangleDecompositionSchemata

/-! Complete finite predicate lists retain all rectangle domains and all
primitive nodes of every Euler tree, without introducing new parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a n : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def OriginalEulerCertificate.predicates (C : OriginalEulerCertificate B sp n) :
    List ((a : ℕ) × GammaDomainFormula B p a sp) :=
  (List.ofFn (fun i => (C.cells i).predicates)).flatten

theorem OriginalEulerCertificate.rowAgreement_iff_predicates (R : GammaParameterRecode B p q sp sq)
    (C : OriginalEulerCertificate B sp n) (z : Fin p → M) (t : Fin q → M) :
    C.RowAgreement R z t ↔ ∀ D ∈ C.predicates, R.DomainAgreement D.2 z t := by
  constructor
  · intro h D hD
    obtain ⟨L,hL,hD⟩ := List.mem_flatten.mp hD
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hL
    exact ((C.cells i).rowAgreement_iff_predicates R z t).mp (h i) D hD
  · intro h i
    apply ((C.cells i).rowAgreement_iff_predicates R z t).mpr
    intro D hD
    exact h D (List.mem_flatten.mpr ⟨(C.cells i).predicates,List.mem_ofFn.mpr ⟨i,rfl⟩,hD⟩)

def RVRectanglePieceSchema.domainPredicates (F : RVRectanglePieceSchema B p a sp) :
    List ((a : ℕ) × GammaDomainFormula B p a sp) :=
  [⟨a,F.source⟩,⟨F.residueArity,F.residue.domain⟩,⟨F.freeArity,F.gamma⟩] ++ F.euler.predicates

theorem RVRectanglePieceSchema.rowAgreement_iff_predicates (R : GammaParameterRecode B p q sp sq)
    (F : RVRectanglePieceSchema B p a sp) (z : Fin p → M) (t : Fin q → M) :
    F.RowAgreement R z t ↔ (∀ D ∈ F.domainPredicates, R.DomainAgreement D.2 z t) ∧ R.RelationAgreement F.graph z t := by
  constructor
  · intro h
    refine ⟨?_,h.2.2.2.2⟩
    intro D hD
    simp only [domainPredicates,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hD
    rcases hD with (rfl | rfl | rfl) | hD
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact (F.euler.rowAgreement_iff_predicates R z t).mp h.2.2.2.1 D hD
  · rintro ⟨hD,hG⟩
    have hs := hD ⟨a,F.source⟩ (by simp only [domainPredicates,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,true_or])
    have hr := hD ⟨F.residueArity,F.residue.domain⟩ (by simp only [domainPredicates,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,true_or,or_true])
    have hg := hD ⟨F.freeArity,F.gamma⟩ (by simp only [domainPredicates,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,true_or,or_true])
    refine ⟨hs,hr,hg,?_,hG⟩
    apply (F.euler.rowAgreement_iff_predicates R z t).mpr
    intro D hDmem
    exact hD D (List.mem_append.mpr (Or.inr hDmem))

end DiamondIntegral.Section5
