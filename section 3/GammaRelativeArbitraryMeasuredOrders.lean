import «section 3».GammaFullRawAllOrderMeasuredValues
import «section 3».GammaStandardRelativeMeasuredValues
import «section 3».GammaNativePointFullMeasuredPermutations

/-! A full measured Gamma map changing the first coordinate of a
specified standard order preserves the literal raw contraction class.
Coordinate permutations use their actual Gamma Jacobian certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRelative_arbitrary_measured_orders
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {n a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfinD : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier D}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (η : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) b)))
    (F : GammaFullMeasuredBijection
      (gammaPointMeasuredData A hA hfinA (gammaPointRetainedForm A hA
        (GammaGroundDefSet.univ hc B (rawRVSpace a)) id (fun _ => Set.mem_univ _) ω))
      (gammaPointMeasuredData D hD hfinD (gammaPointRetainedForm D hD
        (GammaGroundDefSet.univ hc B (rawRVSpace b)) id (fun _ => Set.mem_univ _) η)))
    (i : Fin (n+1)) (hi : ∀ p, ∀ j, j ≠ i → (F.map.map p).val.1 j = p.val.1 j)
    {σ τ : Equiv.Perm (Fin (n+1))}
    (T : StandardContraction A σ) (W : StandardContraction D τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfinA T hT ω) =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hD hfinD W hW η) := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let ν : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
  have hν : ν 0 = i := by simp only [ν,Equiv.swap_apply_left]
  obtain ⟨R,hR,_,_,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr
    hGenerated hBC A hA ν
  obtain ⟨S,hS,_,_,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hr
    hGenerated hBC D hD ν
  have hLeft := gammaFull_raw_all_order_measured_values C hBC hv hg hNames hGenerated δ hδ hδ1 A hA hfinA ω T R hT hR
  have hRight := gammaFull_raw_all_order_measured_values C hBC hv hg hNames hGenerated δ hδ hδ1 D hD hfinD η S W hS hW
  have hMiddle := gammaStandard_relative_measured_values C hBC hv hg δ hδ hδ1 hA hD hfinA hfinD ω η F
    (fun p j hj => hi p j (hν ▸ hj)) R S hR hS
  exact hLeft.trans (hMiddle.trans hRight)

end DiamondIntegral.Section3
