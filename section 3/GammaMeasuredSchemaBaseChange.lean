import «section 3».GammaMeasuredGeometricSchemata
import Integration7.GammaVolumeFormulaBaseChange

/-! Eliminate definable names from complete Gamma density formulas and
their finite proofs. Domains, volumes, densities and bounds stay literal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B C : Base (M := M)}
variable {p a b k : ℕ} {sp : Fin p → SortTag}

def gammaMeasuredSchemaChangeBase (H : GammaFormulaBaseChange C B)
    (F : GammaMeasuredRVSchema hc C p a (k+1) sp) : GammaMeasuredRVSchema hc B p a (k+1) sp :=
  .ofRVTemplate (H.volumeObject F.toRVTemplate)

def gammaMeasuredIsoChangeBase (H : GammaFormulaBaseChange C B)
    (I : GammaMeasuredRVIsoSchema hc C p a b k sp) : GammaMeasuredRVIsoSchema hc B p a b k sp :=
  ⟨gammaMeasuredSchemaChangeBase H I.source,gammaMeasuredSchemaChangeBase H I.target,
    I.chart,H.definable _ _ I.chart_definable⟩

def gammaMeasuredGeometryChangeBase (H : GammaFormulaBaseChange C B) :
    {a b : ℕ} → {F : GammaMeasuredRVSchema hc C p a (k+1) sp} →
      {G : GammaMeasuredRVSchema hc C p b (k+1) sp} → GammaMeasuredRelationSchema F G →
        GammaMeasuredRelationSchema (gammaMeasuredSchemaChangeBase H F) (gammaMeasuredSchemaChangeBase H G)
  | _,_,_,_,.iso I => .iso (gammaMeasuredIsoChangeBase H I)
  | _,_,_,_,.agreement F G => .agreement (gammaMeasuredSchemaChangeBase H F) (gammaMeasuredSchemaChangeBase H G)
  | _,_,_,_,.elementary F N A => .elementary (gammaMeasuredSchemaChangeBase H F) N A
  | _,_,_,_,.symm K => .symm (gammaMeasuredGeometryChangeBase H K)
  | _,_,_,_,.trans E K L => .trans (gammaMeasuredSchemaChangeBase H E)
      (gammaMeasuredGeometryChangeBase H K) (gammaMeasuredGeometryChangeBase H L)
  | _,_,_,_,.coprod K L N R => .coprod (gammaMeasuredGeometryChangeBase H K) (gammaMeasuredGeometryChangeBase H L) N R

theorem gammaMeasuredSchemaChangeBase_valid (H : GammaFormulaBaseChange C B)
    (F : GammaMeasuredRVSchema hc C p a (k+1) sp) (z : Fin p → M) :
    (gammaMeasuredSchemaChangeBase H F).valid z ↔ F.valid z := Iff.rfl

theorem gammaMeasuredIsoChangeBase_valid (H : GammaFormulaBaseChange C B)
    (I : GammaMeasuredRVIsoSchema hc C p a b k sp) (z : Fin p → M) :
    (gammaMeasuredIsoChangeBase H I).valid z ↔ I.valid z := Iff.rfl

theorem gammaMeasuredGeometryChangeBase_valid (H : GammaFormulaBaseChange C B)
    {F : GammaMeasuredRVSchema hc C p a (k+1) sp} {G : GammaMeasuredRVSchema hc C p b (k+1) sp}
    (K : GammaMeasuredRelationSchema F G) (z : Fin p → M) :
    (gammaMeasuredGeometryChangeBase H K).valid z ↔ K.valid z := by
  induction K with
  | iso I => rfl
  | agreement F G => rfl
  | elementary F N A => rfl
  | symm K ih => exact ih
  | trans E K L ihK ihL => exact and_congr ihK ihL
  | coprod K L N R ihK ihL => exact and_congr ihK (and_congr ihL Iff.rfl)

theorem gammaMeasuredSchemaChangeBase_roundtrip (H : GammaFormulaBaseChange B C) (K : GammaFormulaBaseChange C B)
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp) :
    gammaMeasuredSchemaChangeBase K (gammaMeasuredSchemaChangeBase H F) = F := by
  cases F
  rfl

end DiamondIntegral.Section3
