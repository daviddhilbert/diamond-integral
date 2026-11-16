import «section 6».VFScalarNameTemplates
import «section 6».PromotedContinuousRVTemplates

/-! Complete promoted graphs recover the exact original coefficient
and whole focus family at the parameter where they were promoted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r m : ℕ}

theorem vfScalarTemplateValue_of_entry (T : ContinuousVFGraphTemplate (M := M) S p 0 1)
    (a : Fin p → M) (ha : a ∈ T.good) (c : Fin 1 → M)
    (hc : Sum.elim a (Sum.elim (Fin.elim0 : Fin 0 → M) c) ∈ T.graph) :
    c 0=(vfScalarTemplateValue T a ha).val := by
  obtain ⟨x,hx⟩ := (Set.ext_iff.mp (T.value_graph a ha) _).mp hc
  have hInput : x=Fin.elim0 := funext (fun i => i.elim0)
  subst x
  exact (congrFun hx (.inr 0)).symm

theorem ContinuousRVGraphTemplate.value_eq_of_graph
    (T : ContinuousRVGraphTemplate (M := M) S p r n m) (a : Fin p → M) (ha : a ∈ T.good)
    (f : (Fin r → RVInfinity M) → (Fin n → VF M) → Fin m → VF M)
    (hSection : {z | Sum.elim a z ∈ T.graph}=rvVFGraph f)
    (u : Fin r → RVInfinity M) (x : Fin n → VF M) : T.value a ha u x=f u x := by
  have hFamily := (Set.ext_iff.mp hSection _).mp (T.value_mem a ha u x)
  obtain ⟨y,hy⟩ := (Set.ext_iff.mp (rvVFGraph_section f u) _).mp hFamily
  have hyx : y=x := vfValues_injective (by funext i; exact congrFun hy (.inl i))
  subst y
  apply vfValues_injective
  funext i
  exact (congrFun hy (.inr i)).symm

end DiamondIntegral.Section6
