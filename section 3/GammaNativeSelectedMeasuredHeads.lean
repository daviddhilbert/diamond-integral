import «section 3».GammaSelectedMeasuredHeads
import «section 3».GammaNativeAlmostEverywhereJacobians
import Integration7.RelativeHeadSpecialJacobians
import IntegrationSection5.HeadPreparationExtension

/-! Every specified Gamma-definable native head preparation supplies
the actual measured-head certificate used by the contraction induction.
Its checked almost-everywhere special Jacobian descends to the original
ground, and the canonical lift fixes the same VF component. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {S : Set M} {n a k : ℕ}

def gammaNativeSelectedRetainedData
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A))
    (ρ : Fin k → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    GammaSelectedRetainedData hc B n k where
  arity := a
  set := extendBase A (Set.subset_univ _)
  gamma := hA
  select := ρ
  finite := hfin
  labels := Q
  labels_mem := hQ
  form := ω

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativeSelectedMeasuredHead
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (hA : GammaSetDefinable B (carrier A))
    (T : HeadPreparation A) (hTarget : GammaSetDefinable B (carrier T.target))
    (hMap : GammaGraphDefinable B (pointMapGraph T.map))
    (ρ : Fin k → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    GammaSelectedMeasuredHead (gammaNativeSelectedRetainedData A hA ρ hfin Q hQ ω) := by
  let H := T.extendBase (Set.subset_univ _)
  let hH := gamma_coordinateCanonicalImage H.target hTarget 0
  let hΓ := gamma_composition_graph H.map (coordinateCanonicalBijection H.target 0) hMap
    (gamma_coordinateCanonical_graph H.target hTarget 0)
  refine ⟨H,hTarget,hMap,?_⟩
  intro p hp
  let f := Section5.nativeGammaPointBijection (hc := hc) hA hTarget
    (⟨Equiv.ofBijective T.map T.bijective,hMap⟩ : GammaIso B (carrier A) (carrier T.target))
  let g := Section5.nativeGammaPointBijection (hc := hc) hA hH
    (⟨Equiv.ofBijective H.liftMap H.liftMap_bijective,hΓ⟩ : GammaIso B (carrier A) (carrier H.liftSet))
  have hJ := gammaNative_jacobian_one_of_almostEverywhere C hBC hv (Nat.zero_lt_succ n)
    hA hTarget T.map T.bijective hMap (relative_head_special_vf_jacobian_one hc C T.map T.special) p hp
  apply gammaGroundJacobian_transfer_VF C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv f.map g.map _ p hp 1 hJ
  intro q
  rw [Section5.nativeGammaPointBijection_apply,Section5.nativeGammaPointBijection_apply]
  rfl

end DiamondIntegral.Section3
