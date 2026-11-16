import «section 6».MeasuredRVRestrictions

/-! The degree-zero measured RV lifting case. The VF map is the unique
map on the empty tuple, and its determinant is one at every point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def zeroArityLiftVFMap (U : RVObject (M := M) S 0) :
    Map (rvLift U) (DefSet.univ (rawVFSpace (M := M) 0) S) := by
  refine Map.ofCodes (rvLift U) (fun _ => Fin.elim0) (fun _ => Fin.elim0)
    (fun i => i.elim0) (fun c => ⟨Fin.elim0,Subsingleton.elim _ _⟩) ?_
  intro c
  exact funext (fun i => i.elim0)

def zeroArityRVLift {U V : RVObject (M := M) S 0} (e : U ≅ V) :
    Map (rvLift U) (rvLift V) := by
  let f := (zeroArityLiftVFMap U).pair (e.hom.map.comp (liftLabelMap U))
  exact f.corestrict (fun p => ⟨e.hom.map (liftLabelMap U p),rfl,Subsingleton.elim _ _⟩)

theorem zeroArityRVLift_label {U V : RVObject (M := M) S 0} (e : U ≅ V) (p : rvLift U) :
    liftLabelMap V (zeroArityRVLift e p) = e.hom.map (liftLabelMap U p) := by
  apply Subtype.ext
  rfl

theorem zeroArityRVLift_bijective {U V : RVObject (M := M) S 0} (e : U ≅ V) :
    Function.Bijective (zeroArityRVLift e) := by
  have hleft {U V : RVObject (M := M) S 0} (e : U ≅ V) :
      Function.LeftInverse (zeroArityRVLift e.symm) (zeroArityRVLift e) := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · exact funext (fun i => i.elim0)
    · have h := congrArg Subtype.val (SpecialTransformations.Section7.rvIso_inv_apply e (liftLabelMap U p))
      change (e.inv.map (liftLabelMap V (zeroArityRVLift e p))).val = p.val.2
      rw [zeroArityRVLift_label]
      exact h
  exact ⟨(hleft e).injective,(hleft e.symm).surjective⟩

theorem mixedDerivative_zero_arity {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) 0 r) S}
    {B : DefSet (rawMixedSpace (M := M) 0 s) S} (f : Map A B) (p : A) :
    HasMixedVFDerivativeAt f p (LinearMap.id : (Fin 0 → VF M) →ₗ[VF M] (Fin 0 → VF M)) := by
  refine ⟨fun x => x+0,⟨1,fun x hx => ?_⟩,hasVFDerivativeAt_affine LinearMap.id 0 p.val.1⟩
  have he : x = p.val.1 := Subsingleton.elim _ _
  subst x
  refine ⟨p.property,?_⟩
  have hp : (⟨(p.val.1,p.val.2),p.property⟩ : A) = p := Subtype.ext rfl
  rw [hp]
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem lemma_6_31_zero_arity {U V : MeasuredRVObject (M := M) S 0} (e : MeasuredRVIso U V) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧
      (∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap U.object p) /
          gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  refine ⟨zeroArityRVLift e.iso,zeroArityRVLift_bijective e.iso,
    fun p => ⟨liftLabelMap U.object p,rfl,rfl⟩,fun p => ⟨_,mixedDerivative_zero_arity _ p,?_⟩⟩
  rw [LinearMap.toMatrix'_id,Matrix.det_one,zeroArityRVLift_label,e.gamma_jacobian]
  simp only [rvGammaJacobian,rvVolumeGamma,Finset.prod_empty,Finset.univ_eq_empty,div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one,map_one]

end DiamondIntegral.Section6
