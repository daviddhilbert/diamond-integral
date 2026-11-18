import «section 3».GammaNativeSelectedMeasuredHeads
import «section 3».GammaNativeRetainedFullMaps

/-! Selected families with total retained Gamma forms have literal
volume and density rows, independently of the finite bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a k : ℕ}
variable (A : SpecialTransformations.Section5.DefSet (M := M) S n a)
variable (hA : GammaSetDefinable B (carrier A)) (ρ : Fin k → Fin a)
variable (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
variable (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))

def gammaNativeSelectedTotalData : GammaSelectedRetainedData hc B n k :=
  gammaNativeSelectedRetainedData A hA ρ hfin (GammaGroundDefSet.univ hc B (rawRVSpace a))
    (fun _ => Set.mem_univ _) ω

theorem gammaNativeSelectedTotal_volume (N : ℕ) (x : Fin n → VF (M := M))
    (r : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) :
    ((gammaNativeSelectedTotalData A hA ρ hfin ω).schema N).object.rowVolume (vfValues x) r y ↔
      (x,r) ∈ carrier A ∧ r ∘ ρ = y :=
  gammaSelectedLabelSchema_volume A hA ρ x r y

theorem gammaNativeSelectedTotal_density (N : ℕ) (x : Fin n → VF (M := M))
    (r : Fin a → RV (M := M)) (c : (volumeGammaSpace hc).domain) :
    ((gammaNativeSelectedTotalData A hA ρ hfin ω).schema N).rowDensity (vfValues x) r c ↔
      (x,r) ∈ carrier A ∧ (ω ⟨r,Set.mem_univ _⟩).val = (volumeGammaSpace hc).decode c := by
  let U := gammaNativeSelectedTotalData A hA ρ hfin ω
  have hRows := gammaMeasuredSelectedSchema_density U.set U.gamma U.select U.pointForm x r c
  apply hRows.trans
  constructor
  · rintro ⟨q,hq,hω⟩
    refine ⟨hq ▸ q.property,?_⟩
    have he : U.pointForm q = ω ⟨r,Set.mem_univ _⟩ := congrArg ω (Subtype.ext (congrArg Prod.snd hq))
    exact (congrArg Subtype.val he).symm.trans hω
  · rintro ⟨hr,hω⟩
    exact ⟨⟨(x,r),hr⟩,rfl,hω⟩

end DiamondIntegral.Section3
