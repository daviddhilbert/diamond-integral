import IntegrationSection5.CommonRectangleTail
import IntegrationSection5.HeadPreparationExtension
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b l c v : ℕ}
variable {AN : DefSet (M := M) S 1 a} {BN : DefSet (M := M) S 1 b}
variable {AE : DefSet (M := M) S 1 c} {BE : DefSet (M := M) S 1 v}
variable {H : DefSet (M := M) S 1 l}
variable {uN : SpecialBijection AN BN} {ρN : Fin a → Fin l} {EN : Set (Fin a → RV (M := M))}
variable {uE : SpecialBijection AE BE} {ρE : Fin c → Fin (0+1)}

def pairedTailPreparation
    (N : PaddedUnaryBranchExtension (G := G) uN H ρN EN none)
    {ρE : Fin c → Fin N.lift.arity} {ER : Set (Fin c → RV (M := M))}
    (R : PaddedProductCompletion (G := G) uE N.lift.target ρE ER (uN.chain.lastKind N.start)) : HeadPreparation H where
  arity := R.preparation.arity
  target := R.preparation.target
  map := Map.comp R.preparation.map N.map
  special := specialRelativeBoundary_forget (specialRelativeBoundary_comp N.map R.preparation.map 0 N.special R.boundary)
  saturated := R.preparation.saturated

theorem pairedTailPreparation_graph
    (N : PaddedUnaryBranchExtension (G := G) uN H ρN EN none)
    {ρE : Fin c → Fin N.lift.arity} {ER : Set (Fin c → RV (M := M))}
    (R : PaddedProductCompletion (G := G) uE N.lift.target ρE ER (uN.chain.lastKind N.start)) :
    GammaGraphDefinable G (pointMapGraph (pairedTailPreparation N R).map) :=
  gamma_composition_graph N.map R.preparation.map N.graph R.graph

theorem HeadPreparation.castSource_graph {X X' : DefSet (M := M) S 1 l} (T : HeadPreparation X)
    (h : X = X') (hT : GammaGraphDefinable G (pointMapGraph T.map)) :
    GammaGraphDefinable G (pointMapGraph (T.castSource h).map) := by cases h; exact hT

theorem HeadPreparation.castSource_target_gamma {X X' : DefSet (M := M) S 1 l} (T : HeadPreparation X)
    (h : X = X') (hT : GammaSetDefinable G (carrier T.target)) :
    GammaSetDefinable G (carrier (T.castSource h).target) := by cases h; exact hT

variable {m : ℕ} {X : DefSet (M := M) S 2 m}
def twoStageProgram (F : HeadPreparation X) {H : DefSet (M := M) S 1 (1+F.arity)} (U : HeadPreparation H)
    (hH : H = F.contractedSet) : OrderedContractionProgram S X (headImage (U.castSource hH).target) :=
  .step F (.step (U.castSource hH) (.zero (headImage (U.castSource hH).target)))

theorem twoStageProgram_gamma (F : HeadPreparation X) {H : DefSet (M := M) S 1 (1+F.arity)} (U : HeadPreparation H)
    (hH : H = F.contractedSet) (hF : GammaGraphDefinable G (pointMapGraph F.map))
    (hFT : GammaSetDefinable G (carrier F.target)) (hU : GammaGraphDefinable G (pointMapGraph U.map))
    (hUT : GammaSetDefinable G (carrier U.target)) : GammaProgramDefinable G (twoStageProgram F U hH) :=
  ⟨hF,hFT,U.castSource_graph hH hU,U.castSource_target_gamma hH hUT,
    gamma_headImage _ (U.castSource_target_gamma hH hUT)⟩

end IntegrationInACVF.Section5
