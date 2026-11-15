import «section 5».Completed18LocalLift
import «section 5».NativeArbitraryVFPullbackPreparation
import «section 5».NativeZeroStrataPullbacks
import «section 5».NativeVFFinitePartitions

/-! Actual RV-pullback preparation and the finite zero-stratum partition
prove surjectivity on the local positive semiring, before groupification. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5

theorem completed18RingHom_sum {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    (F : R →+* S) (f : ι → R) (s : Finset ι) : F (∑ i∈s,f i)=∑ i∈s,F (f i) :=
  map_sum F.toAddMonoidHom f s

theorem positivePresentationHom_surjective_of_classes {Obj R : Type*} [CommSemiring R]
    (P : PositiveGrothendieck.Presentation Obj) (F : R →+* PositiveGrothendieck.KPlus P)
    (h : ∀ A,∃ x,F x=PositiveGrothendieck.of P A) : Function.Surjective F := by
  intro z
  obtain ⟨p,rfl⟩ := (PositiveGrothendieck.congruence P).mk'_surjective z
  let Q := PositiveGrothendieck.quotientHom P
  change ∃ x,F x=Q p
  induction p using MvPolynomial.induction_on with
  | C n => exact ⟨n,(map_natCast F n).trans (map_natCast Q n).symm⟩
  | add p q hp hq =>
    obtain ⟨x,hx⟩ := hp
    obtain ⟨y,hy⟩ := hq
    exact ⟨x+y,(F.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (Q.map_add p q).symm)⟩
  | mul_X p A hp =>
    obtain ⟨x,hx⟩ := hp
    obtain ⟨y,hy⟩ := h A
    exact ⟨x*y,(F.map_mul x y).trans ((congrArg₂ (· * ·) hx hy).trans (Q.map_mul p (MvPolynomial.X A)).symm)⟩

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {κ : Cardinal}
variable (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)

include hκ hs h00 hr in
theorem completed18PositiveLift_pullback_preimage
    (F : GammaGroundRVPositiveSemiring hc B →+* GammaGroundVFPositiveSemiring hc B)
    (hF : ∀ {k : ℕ} (U : GammaGroundRVObject hc B k),F (gammaGroundRVSemiringClass U)=
      gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))
    (A : GammaGroundFiniteVFObject hc B) (hpull : IsRVPullback A.domain.carrier) :
    ∃ x,F x=gammaGroundVFSemiringClass A := by
  let U (I : Finset (Fin A.vfArity)) : GammaGroundRVObject hc B (Fintype.card I) :=
    nativeVFZeroStratumRVObject hκ.le hs h00 hr A.domain hpull A.finite I
  refine ⟨∑ I : Finset (Fin A.vfArity),gammaGroundRVSemiringClass (U I),?_⟩
  refine (completed18RingHom_sum F (fun I => gammaGroundRVSemiringClass (U I)) Finset.univ).trans ?_
  refine Eq.trans ?_ (nativeVFSemiringClass_finite_partition A (nativeVFZeroStratum A.domain)
    (nativeVFZeroStratum_disjoint A.domain) (nativeVFZeroStratum_cover A.domain)).symm
  apply Finset.sum_congr rfl
  intro I hI
  exact (hF (U I)).trans
    (nativePositiveVFClass_bijection (nativeVFZeroStratum_lift_bijection hκ.le hs h00 hr
      A.domain hpull A.finite I)).symm

include hκ hs h00 hr in
theorem completed18PositiveLift_class_preimage
    (F : GammaGroundRVPositiveSemiring hc B →+* GammaGroundVFPositiveSemiring hc B)
    (hF : ∀ {k : ℕ} (U : GammaGroundRVObject hc B k),F (gammaGroundRVSemiringClass U)=
      gammaGroundVFSemiringClass (gammaGroundObjectLiftFinite U))
    (A : GammaGroundFiniteVFObject hc B) : ∃ x,F x=gammaGroundVFSemiringClass A := by
  obtain ⟨l,Y,⟨e⟩,hpull⟩ := native_arbitrary_vf_pullback_preparation hκ hs h00 hr A.domain
  have hf := (gammaGroundFiniteRVFibres_iff e hκ.le hs h00 hr).mp A.finite
  let D : GammaGroundFiniteVFObject hc B := ⟨A.vfArity,l+A.rvArity,Y,hf⟩
  obtain ⟨x,hx⟩ := completed18PositiveLift_pullback_preimage hκ hs h00 hr F hF D hpull
  exact ⟨x,hx.trans (nativePositiveVFClass_bijection e).symm⟩

theorem completed18LocalLift_surjective : Function.Surjective
    (completed18LocalLift (hc := hc) hκ.le hs h00 hr hB) :=
  positivePresentationHom_surjective_of_classes (gammaGroundVFSemiringPresentation hc B) _
    (completed18PositiveLift_class_preimage hκ hs h00 hr
      (completed18LocalLift hκ.le hs h00 hr hB) (completed18LocalLift_class hκ.le hs h00 hr hB))

end DiamondIntegral.Section5
