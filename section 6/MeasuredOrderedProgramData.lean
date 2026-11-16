import «section 6».RestoredProgramLabelMaps
import «section 6».HeadStartGammaForms

/-! A measured ordered program records an actual Gamma form on its
final RV target and exact factorization of the original source form.
Restored preparation labels give this form through any later program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure MeasuredOrderedProgram
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) where
  arity : ℕ
  rvTarget : DefSet (rawMixedSpace (M := M) 0 arity) S
  program : OrderedStandardContractionProgram (G := G) S A rvTarget
  rvForm : Map rvTarget (DefSet.univ (rawGammaPresentation (M := M)) S)
  factor : ∀ p : A,(rvForm (program.toMap p)).val=(ω p).val

namespace MeasuredOrderedProgram
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

def liftedRVMap (F : MeasuredOrderedProgram (G := G) A ω) (V : OrderedStandardContractionLift F.program) :
    Map V.target F.rvTarget :=
  (rvProjection (Map.id V.target)).corestrict (fun p => ((V.recover p.val).mp p.property).1)

def targetForm (F : MeasuredOrderedProgram (G := G) A ω) (V : OrderedStandardContractionLift F.program) :
    Map V.target (DefSet.univ (rawGammaPresentation (M := M)) S) := F.rvForm.comp (F.liftedRVMap V)

theorem liftedRVMap_commutes (F : MeasuredOrderedProgram (G := G) A ω)
    (V : OrderedStandardContractionLift F.program) (p : A) :
    F.liftedRVMap V (V.map p)=F.program.toMap p := by
  apply Subtype.ext
  exact Prod.ext (by funext i; exact i.elim0) (V.labels p)

theorem targetForm_transport (F : MeasuredOrderedProgram (G := G) A ω)
    (V : OrderedStandardContractionLift F.program) (p : A) :
    (F.targetForm V (V.map p)).val=(ω p).val := by
  change (F.rvForm (F.liftedRVMap V (V.map p))).val=_
  rw [F.liftedRVMap_commutes]
  exact F.factor p

theorem targetForm_same_tags (F : MeasuredOrderedProgram (G := G) A ω)
    (V : OrderedStandardContractionLift F.program) (p z : V.target) (hTags : p.val.2=z.val.2) :
    F.targetForm V p=F.targetForm V z := by
  apply congrArg F.rvForm
  apply Subtype.ext
  exact Prod.ext (by funext i; exact i.elim0) hTags

def of_restored_preparation
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (T : MeasuredCoordinatePreparation (G := G) A C hCA ω) (D : RestoredStageLabelData (G := G) T.map)
    {q : ℕ} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (tail : OrderedStandardContractionProgram (G := G) S D.stage.contracted U) :
    MeasuredOrderedProgram (G := G) A ω := by
  have hConst (p z : T.target) (hTags : p.val.2=z.val.2) : T.form p=T.form z := by
    apply Subtype.ext
    have h := T.constant p.val p.property z.val z.property hTags
    rw [gammaFormExtension_at T.form p,gammaFormExtension_at T.form z] at h
    exact h
  let ψ := headStartRVForm T.target 0 Fin.elim0 T.form hConst
  refine {
    arity := q
    rvTarget := U
    program := .step D.stage tail
    rvForm := ψ.comp (D.finalOldTags tail)
    factor := ?_ }
  intro p
  have hLabel : D.finalOldTags tail ((OrderedStandardContractionProgram.step D.stage tail).toMap p)=
      pureRVTagQuotient T.target (T.map p) := Subtype.ext (D.finalOldTags_commutes tail p)
  change (ψ (D.finalOldTags tail ((OrderedStandardContractionProgram.step D.stage tail).toMap p))).val=_
  rw [hLabel]
  have h := headStartRVForm_at T.target 0 Fin.elim0 T.form hConst (T.map p)
  exact (congrArg Subtype.val h).trans (T.transport p)

end MeasuredOrderedProgram
end DiamondIntegral.Section6
