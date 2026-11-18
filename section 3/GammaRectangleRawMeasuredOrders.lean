import «section 3».GammaNativeFiniteCodeExtensions
import Integration7.RectangleFamilyGammaOrderIsomorphisms

/-! The two constructed rectangle orders are actually Gamma-measured
RV isomorphic for every total retained Gamma form. The proof reuses
the full coordinate and every-old-label identities of the RV-density
rectangle construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {m : ℕ}

def gammaRectangle_raw_measured_orders
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {H : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
    (hH : GammaSetDefinable B (carrier H))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier H}.Finite)
    {hRect : RectangularRVFibres (carrier H)} (F : IndependentRectangleFamilyPreparations B H hRect)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) m))) :
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let U := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hH hfin
      F.headContraction (F.head_contraction_gamma hH))
    let V := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hH hfin
      F.tailContraction (F.tail_contraction_gamma hH))
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization U
        (gammaNativeTotalRVForm U (suffixIndex F.headContraction.program.rvArity_le) ω))
      (gammaNativeMeasuredNormalization V
        (gammaNativeTotalRVForm V (suffixIndex F.tailContraction.program.rvArity_le) ω)) := by
  intro hr U V
  let e := F.rawGammaOrderIso C.uncountable.le C.saturated hr hc C hBC hH hfin
  apply gammaNativeRetainedRVHom (GammaGroundDefSet.univ hc B (rawRVSpace m))
    (suffixIndex F.headContraction.program.rvArity_le) (suffixIndex F.tailContraction.program.rvArity_le)
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) ω (gammaNativeFiniteIso e)
  · intro u
    exact congrArg (fun t : Fin 2 → RV (M := M) => ∏ i, Values.vrv (t i))
      (F.raw_gamma_order_coordinates C.uncountable.le C.saturated hr hc C hBC hH hfin u)
  · intro u
    funext i
    exact F.raw_gamma_order_retained_labels C.uncountable.le C.saturated hr hc C hBC hH hfin i u

end DiamondIntegral.Section3
