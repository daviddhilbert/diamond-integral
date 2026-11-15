import «section 5».Completed18VFObjects
import «section 3».PresentationHomExt
import IntegrationSection6.GammaMixedEmptyIsomorphisms

/-! The actual positive VF presentations agree. Union/intersection
relations are obtained from partitions, including empty sets in every arity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

abbrev completed18VFClass (A : GammaVFAllFiniteObject B) : GammaVFAllKPlus B :=
  PositiveGrothendieck.of (gammaVFAllPositivePresentation B) A

theorem completed18VFClass_iso {A C : GammaVFAllFiniteObject B} (e : GammaIso B A.domain C.domain) :
    completed18VFClass A=completed18VFClass C := PositiveGrothendieck.of_iso _ ⟨e⟩

theorem nativeVFGround_scissor {A C D E : GammaVFAllFiniteObject B} (h : GammaVFAllScissor A C D E) :
    gammaGroundVFSemiringClass (nativeVFGroundObject (hc := hc) A)+
      gammaGroundVFSemiringClass (nativeVFGroundObject C)=
    gammaGroundVFSemiringClass (nativeVFGroundObject D)+
      gammaGroundVFSemiringClass (nativeVFGroundObject E) := by
  rcases A with ⟨⟨n,r⟩,A,hA,fA⟩
  rcases C with ⟨c,C,hC,fC⟩
  rcases D with ⟨d,D,hD,fD⟩
  rcases E with ⟨e,E,hE,fE⟩
  rcases h with ⟨hc',hd,he,hu,hi⟩
  change (n,r)=c at hc'
  change (n,r)=d at hd
  change (n,r)=e at he
  subst c; subst d; subst e
  obtain ⟨rfl,rfl⟩ := (gammaVFAllScissor_domains A C D E hA hC hD hE fA fC fD fE).mp ⟨rfl,rfl,rfl,hu,hi⟩
  exact groundVFClass_union_inter (nativeGammaPointDomain A hA) (nativeGammaPointDomain C hC) fA fC

def nativeVFPositiveGroundInvariant : PositiveGrothendieck.Invariant (gammaVFAllPositivePresentation B)
    (R := GammaGroundVFPositiveSemiring hc B) where
  toFun A := gammaGroundVFSemiringClass (nativeVFGroundObject A)
  iso {a b} h := by
    obtain ⟨e⟩ := h
    exact nativePositiveVFClass_bijection (nativeGammaPointBijection a.definable b.definable e)
  empty := gammaGroundVFSemiringClass_empty
  unit := gammaGroundVFSemiringClass_unit
  product A C := by
    apply Eq.trans _ (gammaGroundVFSemiringClass_product (nativeVFGroundObject A) (nativeVFGroundObject C))
    apply nativePositiveVFClass_bijection
    apply GammaGroundBijection.ofCarrierEq
    exact (groundVFNative_product_domain (nativeVFGroundObject (hc := hc) A) (nativeVFGroundObject C)).symm
  scissor := nativeVFGround_scissor

def nativeVFPositiveGround : GammaVFAllKPlus B →+* GammaGroundVFPositiveSemiring hc B :=
  PositiveGrothendieck.lift (gammaVFAllPositivePresentation B) nativeVFPositiveGroundInvariant

theorem nativeVFPositiveGround_class (A : GammaVFAllFiniteObject B) :
    nativeVFPositiveGround (completed18VFClass A)=gammaGroundVFSemiringClass (nativeVFGroundObject (hc := hc) A) :=
  PositiveGrothendieck.lift_of _ _ A

theorem groundVFNative_partition (A : GammaGroundFiniteVFObject hc B)
    (X : GammaGroundDefSet hc B (rawMixedSpace (M := M) A.vfArity A.rvArity))
    (hX : X.carrier ⊆ A.domain.carrier) :
    completed18VFClass (groundVFNativeObject (A.restrict X hX))+
      completed18VFClass (groundVFNativeObject (A.restrict (A.domain.sdiff X) (fun _ h => h.1)))=
    completed18VFClass (groundVFNativeObject A) := by
  let Z : GammaVFAllFiniteObject B :=
    ⟨(A.vfArity,A.rvArity),∅,groundMixed_gamma_set (GammaGroundDefSet.empty hc B _),fun _ => Set.finite_empty⟩
  have hz : completed18VFClass Z=0 :=
    (completed18VFClass_iso (gammaEmptyMixedIso rfl rfl)).trans (PositiveGrothendieck.of_empty _)
  have hs : GammaVFAllScissor
      (groundVFNativeObject (A.restrict X hX))
      (groundVFNativeObject (A.restrict (A.domain.sdiff X) (fun _ h => h.1)))
      (groundVFNativeObject A) Z := by
    apply (gammaVFAllScissor_domains _ _ _ _ _ _ _ _ _ _ _ _).mpr
    constructor
    · ext x
      change x∈A.domain.carrier ↔ (x∈X.carrier ∨ x∈A.domain.carrier ∧ x∉X.carrier)
      exact ⟨fun hx => (Classical.em (x∈X.carrier)).elim Or.inl (fun hn => Or.inr ⟨hx,hn⟩),
        fun hx => hx.elim (fun h => hX h) And.left⟩
    · ext x
      change False ↔ (x∈X.carrier ∧ x∈A.domain.carrier ∧ x∉X.carrier)
      tauto
  have h := PositiveGrothendieck.of_scissor (gammaVFAllPositivePresentation B) hs
  simpa only [hz,add_zero] using h

def groundVFNativeInvariant : PositiveGrothendieck.Invariant (gammaGroundVFSemiringPresentation hc B)
    (R := GammaVFAllKPlus B) where
  toFun A := completed18VFClass (groundVFNativeObject A)
  iso h := by
    obtain ⟨e⟩ := h
    exact completed18VFClass_iso (groundMixed_gamma_iso e.hom)
  empty := PositiveGrothendieck.of_empty _
  unit := PositiveGrothendieck.of_unit _
  product A C := by
    apply Eq.trans _ (PositiveGrothendieck.of_product (gammaVFAllPositivePresentation B) _ _)
    apply completed18VFClass_iso
    exact (gammaIso_reflexive _ (groundVFNativeObject (A.product C)).definable).congr rfl
      (groundVFNative_product_domain A C)
  scissor {a b d e} h := by
    obtain ⟨U,X,hX,ha,hb,hd,he⟩ := h
    subst a b d e
    change completed18VFClass (groundVFNativeObject (U.restrict X hX))+
      completed18VFClass (groundVFNativeObject (U.restrict (U.domain.sdiff X) (fun _ h => h.1)))=
      completed18VFClass (groundVFNativeObject U)+completed18VFClass (gammaVFAllEmpty B)
    rw [groundVFNative_partition]
    rw [show completed18VFClass (gammaVFAllEmpty B)=0 from PositiveGrothendieck.of_empty _,add_zero]

def groundVFNativePositive : GammaGroundVFPositiveSemiring hc B →+* GammaVFAllKPlus B :=
  PositiveGrothendieck.lift (gammaGroundVFSemiringPresentation hc B) groundVFNativeInvariant

theorem groundVFNativePositive_class (A : GammaGroundFiniteVFObject hc B) :
    groundVFNativePositive (gammaGroundVFSemiringClass A)=completed18VFClass (groundVFNativeObject A) :=
  PositiveGrothendieck.lift_of _ _ A

def completed18VFPositiveEquiv : GammaGroundVFPositiveSemiring hc B ≃+* GammaVFAllKPlus B := by
  have h₁ : (nativeVFPositiveGround (hc := hc) (B := B)).comp groundVFNativePositive=RingHom.id _ := by
    apply positivePresentationHom_ext (gammaGroundVFSemiringPresentation hc B)
    intro A
    change nativeVFPositiveGround (groundVFNativePositive (gammaGroundVFSemiringClass A))=_
    rw [groundVFNativePositive_class,nativeVFPositiveGround_class]
    exact nativePositiveVFClass_bijection (groundVFObjectRoundTrip A)
  have h₂ : (groundVFNativePositive (hc := hc) (B := B)).comp nativeVFPositiveGround=RingHom.id _ := by
    apply PositiveGrothendieck.hom_ext (gammaVFAllPositivePresentation B)
    intro A
    change groundVFNativePositive (nativeVFPositiveGround (completed18VFClass A))=_
    rw [nativeVFPositiveGround_class,groundVFNativePositive_class]
    exact completed18VFClass_iso (nativeVFObjectRoundTrip A)
  exact RingEquiv.ofRingHom groundVFNativePositive nativeVFPositiveGround h₂ h₁

end DiamondIntegral.Section5
