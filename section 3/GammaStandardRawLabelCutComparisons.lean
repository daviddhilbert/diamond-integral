import «section 3».GammaNativeGroundHighRestriction
import «section 3».GammaNativeEndpointRawClasses
import «section 3».GammaNativeMeasuredScissors
import Integration7.StandardTargetRestrictionPresentations

/-! Literal raw contraction restrictions keep the original structural
coordinates and retained Gamma form. These identities support measured
scissors for the existing finite cell-family partitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def gammaNativeGroundCoordinateHom
    {U V : GammaObjectAt B Set.univ (n+1)}
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (f : GammaGroundBijection (Section5.nativeRVGroundDomain (hc := hc) U) (Section5.nativeRVGroundDomain V))
    (hVolume : ∀ u, (Section5.nativeRVGroundVolume V (f.map u)).val = (Section5.nativeRVGroundVolume U u).val)
    (hForm : ∀ u, η (f.map u) = ω u) :
    GammaGroundMeasuredRVHom (gammaNativeMeasuredNormalization U ω) (gammaNativeMeasuredNormalization V η) := by
  apply gammaNativeGroundMeasuredHom ω η f
  · intro u
    rw [gammaNativeHigh_domain_nonzero,gammaNativeHigh_domain_nonzero]
    constructor
    · rintro ⟨v,hv,hn⟩
      have he : v = u := Subtype.ext hv
      subst v
      refine ⟨f.map u,rfl,?_⟩
      rw [hVolume]
      exact hn
    · rintro ⟨v,hv,hn⟩
      have he : v = f.map u := Subtype.ext hv
      subst v
      refine ⟨u,rfl,?_⟩
      rw [hVolume] at hn
      exact hn
  · intro u
    unfold gammaNativeCombinedWeight
    rw [hVolume]
    exact congrArg (fun q : GammaGroundDefSet.univ hc B (volumeGammaSpace hc) =>
      (cast (gammaCarrier hc) q.val).val * ∏ i, Values.vrv ((Section5.nativeRVGroundVolume U u).val i)) (hForm u).symm

variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M)) {a d : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
variable (hA : GammaSetDefinable B (carrier A))
variable (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
variable {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)

theorem gammaNative_raw_contraction_mem (r : Fin T.arity → RV (M := M)) :
    r ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaNativeFiniteAt
      (gammaRawFiniteContraction C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hBC hA hfin T hT))).carrier ↔
      (Fin.elim0,r) ∈ carrier T.target := by
  rw [Section5.nativeRVGroundDomain_carrier]
  change r ∈ carrier (SpecialTransformations.Section5.Map.image (rawLabelMap T.target)) ↔ _
  constructor
  · rintro ⟨p,hp⟩
    have he : p.val = (Fin.elim0,r) := Prod.ext (Subsingleton.elim _ _) hp
    exact he ▸ p.property
  · intro hr
    exact ⟨⟨(Fin.elim0,r),hr⟩,rfl⟩

end DiamondIntegral.Section3
