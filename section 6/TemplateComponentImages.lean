import «section 6».TemplateComponentFamilies
import «section 6».FocusComponentImageTemplates

/-! Exact local first-component image templates for an actual
component family. Injectivity identifies every full protected image
with membership in its original protected fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {K : FocusComponentParameterTemplate (M := M) S 1 n s}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {hGood : ∀ b : B,unaryFamilyParameter η b ∈ K.good A P}
namespace TemplateComponentFamily
variable (L : TemplateComponentFamily (G := G) η K A P hGood)

theorem target_fibre (b : B) :
    (((CentripetalProgramTemplate.centripetal K).target A).fibre (unaryFamilyParameter η b))=
      (L.component b).map.image :=
  K.imageTemplate_at A _ (hGood b).1.1.1 (hGood b).1.1.2 (L.component b)
    (L.coordinate b) (L.active b) (L.coefficient b) (L.focus b)

theorem pieceTarget_fibre (b : B) (i : Fin k)
    (hPA : ((P i).fibre (unaryFamilyParameter η b)).carrier ⊆ (A.fibre (unaryFamilyParameter η b)).carrier) :
    (((CentripetalProgramTemplate.centripetal K).pieceTarget A (P i)).fibre (unaryFamilyParameter η b))=
      ((L.component b).bijection.restrict hPA).image :=
  K.pieceImageTemplate_at A (P i) _ (hGood b).1.1.1 (hGood b).1.1.2 (L.component b)
    (L.coordinate b) (L.active b) (L.coefficient b) (L.focus b) hPA

theorem pieceTarget_mem_iff (h00 : M ⊨ Axioms.ACVF00) (b : B) (i : Fin k)
    (hPA : ((P i).fibre (unaryFamilyParameter η b)).carrier ⊆ (A.fibre (unaryFamilyParameter η b)).carrier)
    (x : Mixed M n s) (hx : x ∈ (A.fibre (unaryFamilyParameter η b)).carrier) :
    (L.component b).point x ∈
      (((CentripetalProgramTemplate.centripetal K).pieceTarget A (P i)).fibre (unaryFamilyParameter η b)).carrier ↔
        x ∈ ((P i).fibre (unaryFamilyParameter η b)).carrier := by
  rw [L.pieceTarget_fibre b i hPA]
  constructor
  · rintro ⟨p,hp⟩
    have he := (L.component b).point_injective_on h00 (hPA p.property) hx hp
    exact he ▸ p.property
  · intro hp
    exact ⟨⟨x,hp⟩,rfl⟩

end TemplateComponentFamily
end DiamondIntegral.Section6
