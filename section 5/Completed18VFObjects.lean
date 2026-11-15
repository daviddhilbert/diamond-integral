import «section 5».NativeGammaPointBridge
import «section 5».Completed18GroundCodeGraphs
import «section 5».NativeVFGroundTransfer
import IntegrationSection6.GammaVFAllScissorDomains

/-! Actual mixed VF objects and bijections in the completed [18]
presentation and the local Gamma-ground presentation. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r m s : ℕ}

theorem groundMixed_gamma_set (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    GammaSetDefinable B D.carrier := nativeMixedDomain_definable D

def groundMixed_gamma_iso
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {E : GammaGroundDefSet hc B (rawMixedSpace (M := M) m s)}
    (f : GammaGroundBijection D E) : GammaIso B D.carrier E.carrier where
  equiv := Equiv.ofBijective f.map f.bijective
  graph := by
    have he : {z : Fin ((n+r)+(m+s)) → M | ∃ p : Point (M := M) n r,
        ∃ q : Point (M := M) m s,(∃ u : D,u.val=p ∧ (f.map u).val=q) ∧
          Fin.append (gammaPointCode p) (gammaPointCode q)=z} = nativeMixedGraph f := by
      ext w
      constructor
      · rintro ⟨p,q,⟨u,hu,hv⟩,he⟩
        exact ⟨u,by rw [hu,hv]; exact he.symm⟩
      · rintro ⟨u,hu⟩
        exact ⟨u.val,(f.map u).val,⟨u,rfl,rfl⟩,hu.symm⟩
    exact (congrArg (fun W : Set (Fin ((n+r)+(m+s)) → M) =>
      DefinableOverBase B (Fin.append (gammaPointSort n r) (gammaPointSort m s)) W) he).mpr
        (nativeMixedGraph_definable f)

def groundVFNativeObject (A : GammaGroundFiniteVFObject hc B) : GammaVFAllFiniteObject B :=
  ⟨(A.vfArity,A.rvArity),A.domain.carrier,groundMixed_gamma_set A.domain,A.finite⟩

def nativeVFGroundObject (A : GammaVFAllFiniteObject B) : GammaGroundFiniteVFObject hc B :=
  ⟨A.arity.1,A.arity.2,nativeGammaPointDomain A.domain A.definable,A.finiteFibres⟩

def groundVFObjectRoundTrip (A : GammaGroundFiniteVFObject hc B) :
    GammaGroundBijection (nativeVFGroundObject (groundVFNativeObject A)).domain A.domain :=
  GammaGroundBijection.ofCarrierEq rfl

def nativeVFObjectRoundTrip (A : GammaVFAllFiniteObject B) :
    GammaIso B (groundVFNativeObject (nativeVFGroundObject (hc := hc) A)).domain A.domain :=
  gammaIso_reflexive A.domain A.definable

theorem groundVFNative_product_domain (A C : GammaGroundFiniteVFObject hc B) :
    (groundVFNativeObject (A.product C)).domain =
      (gammaVFAllProduct (groundVFNativeObject A) (groundVFNativeObject C)).domain := by
  ext x
  exact mem_gammaGroundMixedProductDomain A.domain C.domain x

theorem groundVFClass_partition (A : GammaGroundFiniteVFObject hc B)
    (X : GammaGroundDefSet hc B (rawMixedSpace (M := M) A.vfArity A.rvArity))
    (hx : X.carrier ⊆ A.domain.carrier) :
    gammaGroundVFSemiringClass (A.restrict X hx)+
      gammaGroundVFSemiringClass (A.restrict (A.domain.sdiff X) (fun _ h => h.1))=
        gammaGroundVFSemiringClass A := by
  have h := gammaGroundVFSemiringClass_scissor ⟨A,X,hx,rfl,rfl,rfl,rfl⟩
  simpa only [gammaGroundVFSemiringClass_empty,add_zero] using h

theorem groundVFClass_union_inter
    (D E : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (fD : ∀ x,{t | (x,t)∈D.carrier}.Finite) (fE : ∀ x,{t | (x,t)∈E.carrier}.Finite) :
    gammaGroundVFSemiringClass (⟨n,r,D,fD⟩ : GammaGroundFiniteVFObject hc B)+
      gammaGroundVFSemiringClass (⟨n,r,E,fE⟩ : GammaGroundFiniteVFObject hc B)=
    gammaGroundVFSemiringClass (⟨n,r,D.union E,fun x => (fD x).union (fE x)⟩ : GammaGroundFiniteVFObject hc B)+
      gammaGroundVFSemiringClass (⟨n,r,D.inter E,fun x => (fD x).subset (fun _ h => h.1)⟩ : GammaGroundFiniteVFObject hc B) := by
  let A : GammaGroundFiniteVFObject hc B := ⟨n,r,D,fD⟩
  let C : GammaGroundFiniteVFObject hc B := ⟨n,r,E,fE⟩
  let U : GammaGroundFiniteVFObject hc B := ⟨n,r,D.union E,fun x => (fD x).union (fE x)⟩
  let I : GammaGroundFiniteVFObject hc B := ⟨n,r,D.inter E,fun x => (fD x).subset (fun _ h => h.1)⟩
  have hU := groundVFClass_partition U D (fun _ h => Or.inl h)
  have hC := groundVFClass_partition C (D.inter E) (fun _ h => h.2)
  have ha : gammaGroundVFSemiringClass (U.restrict D (fun _ h => Or.inl h)) = gammaGroundVFSemiringClass A :=
    nativePositiveVFClass_bijection (GammaGroundBijection.ofCarrierEq rfl)
  have hi : gammaGroundVFSemiringClass (C.restrict (D.inter E) (fun _ h => h.2)) = gammaGroundVFSemiringClass I :=
    nativePositiveVFClass_bijection (GammaGroundBijection.ofCarrierEq rfl)
  have hq : gammaGroundVFSemiringClass (U.restrict (U.domain.sdiff D) (fun _ h => h.1)) =
      gammaGroundVFSemiringClass (C.restrict (C.domain.sdiff (D.inter E)) (fun _ h => h.1)) := by
    apply nativePositiveVFClass_bijection
    apply GammaGroundBijection.ofCarrierEq
    ext x
    change ((x∈D.carrier ∨ x∈E.carrier) ∧ x∉D.carrier) ↔
      (x∈E.carrier ∧ ¬(x∈D.carrier ∧ x∈E.carrier))
    tauto
  rw [ha,hq] at hU
  rw [hi] at hC
  change gammaGroundVFSemiringClass A+gammaGroundVFSemiringClass C=
    gammaGroundVFSemiringClass U+gammaGroundVFSemiringClass I
  rw [← hU,← hC]
  ac_rfl

end DiamondIntegral.Section5
