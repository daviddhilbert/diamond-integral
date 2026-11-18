import «section 3».GammaMeasuredRVSyntax
import Integration7.GammaVolumeGammaValidity
import Integration7.EssentialFiniteVolumeSchemata
import IntegrationSection6.GammaIsomorphismSchemata

/-! Gamma-valued measured chart witnesses reuse the native finite
isomorphism and Gamma-weight predicates verbatim. Complete density code
relations are checked by quotient validity; no RV Jacobian clause or RV
representative function is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaMeasuredRVIsoSchema (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (p a b k : ℕ) (sp : Fin p → SortTag := fun _ => .rv) where
  source : GammaMeasuredRVSchema hc B p a (k+1) sp
  target : GammaMeasuredRVSchema hc B p b (k+1) sp
  chart : Set (Fin ((p+a)+b) → M)
  chart_definable : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) chart

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaMeasuredRVIsoSchema.ordinary (F : GammaMeasuredRVIsoSchema hc B p a b k sp) :
    GammaFiniteRVIsoSchema B p a b (k+1) sp where
  source := essentialFiniteVolumeSchema F.source.object
  target := essentialFiniteVolumeSchema F.target.object
  chart := F.chart
  chart_definable := F.chart_definable

def GammaMeasuredRVIsoSchema.valid (F : GammaMeasuredRVIsoSchema hc B p a b k sp) (z : Fin p → M) : Prop :=
  F.source.valid z ∧ F.target.valid z ∧ F.ordinary.valid z ∧
    volumeChartGammaRowValid F.source.toRVTemplate F.target.toRVTemplate F.chart z

theorem GammaMeasuredRVIsoSchema.valid_definable (F : GammaMeasuredRVIsoSchema hc B p a b k sp) :
    DefinableOverBase B sp {z | F.valid z} :=
  F.source.valid_definable.inter (F.target.valid_definable.inter (F.ordinary.valid_definable.inter
    (volumeChartGammaRowValid_definable hc F.source.toRVTemplate F.target.toRVTemplate F.chart_definable)))

end DiamondIntegral.Section3
