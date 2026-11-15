import «section 5».NativeWeakPullbackPresentations
import «section 5».NativeWeakRVLabelGraphs

/-! Bounded integration of an RV[<=k] lift is the raw bounded value of
its full RV domain, including every zero-label stratum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}

theorem nativeWeakRVObjectLift_pullback (U : NativeWeakRVObject hc B k) :
    IsRVPullback (nativeWeakRVObjectLift U).carrier := by
  apply (isRVPullback_iff _).mpr
  intro x hx y hxy
  obtain ⟨u,hu,hv⟩ := hx
  have hk := (sameRV_iff x y).mp hxy
  refine ⟨u,hu.trans hk.2,?_⟩
  exact hv.trans (funext hk.1)

theorem nativeWeakLiftKey_graph (U : NativeWeakRVObject hc B k)
    (t : (nativeMixedFullKeyMap (nativeWeakRVObjectLift U)).image) :
    ∃ u : U.domain,t.val = Fin.append (U.volume u).val u.val := by
  obtain ⟨a,ha⟩ := t.property
  obtain ⟨u,hu,hv⟩ := a.property
  refine ⟨u,?_⟩
  exact ha.symm.trans ((nativeMixedFullKeyMap_value _ a).trans (congrArg₂ Fin.append hv.symm hu.symm))

def nativeWeakLiftKeyMap (U : NativeWeakRVObject hc B k) :
    GammaGroundMap (nativeMixedFullKeyMap (nativeWeakRVObjectLift U)).image U.domain :=
  (gammaGroundRVSelectCoordinates (Fin.natAdd k) (nativeMixedFullKeyMap (nativeWeakRVObjectLift U)).image).corestrict
    (by
      intro t
      obtain ⟨u,hu⟩ := nativeWeakLiftKey_graph U t
      change t.val ∘ Fin.natAdd k ∈ U.domain.carrier
      have he : t.val ∘ Fin.natAdd k = u.val := by
        rw [hu]
        exact funext (fun i => Fin.append_right _ _ i)
      exact he.symm ▸ u.property)

def nativeWeakLiftKeyBijection (U : NativeWeakRVObject hc B k) :
    GammaGroundBijection (nativeMixedFullKeyMap (nativeWeakRVObjectLift U)).image U.domain where
  map := nativeWeakLiftKeyMap U
  bijective := by
    constructor
    · intro t s he
      obtain ⟨u,hu⟩ := nativeWeakLiftKey_graph U t
      obtain ⟨v,hv⟩ := nativeWeakLiftKey_graph U s
      have hh : t.val ∘ Fin.natAdd k = s.val ∘ Fin.natAdd k := congrArg Subtype.val he
      have huv : u = v := by
        apply Subtype.ext
        funext i
        have h := congrFun hh i
        simpa only [hu,hv,Function.comp_apply,Fin.append_right] using h
      subst v
      exact Subtype.ext (hu.trans hv.symm)
    · intro u
      obtain ⟨x,hx⟩ := Section2.tupleRV_surjective (U.volume u).val
      let a : nativeWeakRVObjectLift U := ⟨(x,u.val),u,rfl,hx.symm⟩
      refine ⟨(nativeMixedFullKeyMap (nativeWeakRVObjectLift U)).toImage a,?_⟩
      apply Subtype.ext
      change Fin.append (Section2.tupleRV M x) u.val ∘ Fin.natAdd k = u.val
      exact funext (fun i => Fin.append_right _ _ i)

variable {G : GammaGroundContext M}
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable (H : YinGammaGroundUnmeasuredLiftInput G hc)

theorem nativeVFBoundedValue_weak_lift (U : NativeWeakRVObject hc G.base k) :
    nativeVFBoundedValue linear H (nativeVFClass
      (⟨k,U.arity,nativeWeakRVObjectLift U,nativeWeakRVObjectLift_finite U⟩ : GammaGroundFiniteVFObject hc G.base)) =
    nativeRVSetValue G.model00 linear G.uncountable.le G.saturated hc G.base
      G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded U.domain :=
  (nativeVFBoundedValue_pullback linear H _ (nativeWeakRVObjectLift_pullback U)).trans
    (nativeRVSetValue_bijection G.model00 linear G.uncountable.le G.saturated hc G.base
      G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded _ _ (nativeWeakLiftKeyBijection U))

theorem nativeVFBoundedValue_of_weak_lift_bijection (A : GammaGroundFiniteVFObject hc G.base)
    (U : NativeWeakRVObject hc G.base k) (e : GammaGroundBijection A.domain (nativeWeakRVObjectLift U)) :
    nativeVFBoundedValue linear H (nativeVFClass A) =
    nativeRVSetValue G.model00 linear G.uncountable.le G.saturated hc G.base
      G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded U.domain :=
  (congrArg (nativeVFBoundedValue linear H) (nativeVFClass_bijection A
    (⟨k,U.arity,nativeWeakRVObjectLift U,nativeWeakRVObjectLift_finite U⟩ : GammaGroundFiniteVFObject hc G.base) e)).trans
      (nativeVFBoundedValue_weak_lift linear H U)

end DiamondIntegral.Section5
