import «section 6».VFCoordinateReindexing
import «section 6».RVReindexingLifts
import «section 6».SurjectiveMapDescent

/-! Coordinate relabeling on arbitrary proper mixed sources, with the
actual full map, proper covariant homeomorphism and total derivative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def vfRelabeling (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n)) :=
  (reindexVFMap A e).toImage

theorem vfRelabeling_value (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n)) (p : A) :
    (vfRelabeling A e p).val=(p.val.1 ∘ e,p.val.2) := rfl

theorem vfRelabeling_bijective (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n)) :
    Function.Bijective (vfRelabeling A e) := by
  refine ⟨?_,map_toImage_surjective _⟩
  intro p z he
  have hVF := congrArg (fun q => q.val.1) he
  have hTags := congrArg (fun q => q.val.2) he
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have h := congrFun hVF (e.symm i)
    simpa only [vfRelabeling_value,Function.comp_apply,Equiv.apply_symm_apply] using h
  · exact hTags

theorem vfRelabeling_graph_source (A : DefSet (rawMixedSpace (M := M) n r) S)
    (e : Equiv.Perm (Fin n)) (u v : Fin r → RVInfinity M) :
    graphFibreSource (vfRelabeling A e) u v=if u=v then vfFibre A.carrier u else ∅ := by
  ext x
  constructor
  · rintro ⟨y,p,hp,hfp⟩
    have hTags : u=v := (congrArg Prod.snd hp).symm.trans (congrArg Prod.snd hfp)
    rw [if_pos hTags]
    change (x,u) ∈ A.carrier
    exact hp ▸ p.property
  · intro hx
    split_ifs at hx with hTags
    · exact ⟨x ∘ e,⟨(x,u),hx⟩,rfl,Prod.ext rfl hTags⟩
    · exact False.elim hx

theorem vfRelabeling_graph_range (A : DefSet (rawMixedSpace (M := M) n r) S)
    (e : Equiv.Perm (Fin n)) (u v : Fin r → RVInfinity M) :
    graphFibreRange (vfRelabeling A e) u v=if u=v then vfFibre (reindexedVFSet A e).carrier v else ∅ := by
  ext y
  constructor
  · rintro ⟨x,p,hp,hfp⟩
    have hTags : u=v := (congrArg Prod.snd hp).symm.trans (congrArg Prod.snd hfp)
    rw [if_pos hTags]
    change (y,v) ∈ (reindexedVFSet A e).carrier
    exact hfp ▸ (vfRelabeling A e p).property
  · intro hy
    split_ifs at hy with hTags
    · obtain ⟨p,hp⟩ := hy
      have hRV : p.val.2=u := (congrArg Prod.snd hp).trans hTags.symm
      exact ⟨p.val.1,p,Prod.ext rfl hRV,hp⟩
    · exact False.elim hy

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfRelabeling_continuous (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n)) :
    ContinuousOnGraphFibres (vfRelabeling A e) := by
  intro u v
  have hCont : Continuous (fun x : Fin n → VF M => x ∘ e) := continuous_pi (fun i => continuous_apply (e i))
  apply hCont.continuousOn.congr
  intro x hx
  obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph (vfRelabeling A e) u v hx
  exact (congrArg Prod.fst hfp).symm.trans (congrArg (fun a => a ∘ e) (congrArg Prod.fst hp))

theorem vfRelabeling_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n))
    (hA : ProperInvariant S A.carrier) : ProperCovariantHomeomorphism (vfRelabeling A e) := by
  have hB := reindexedVFSet_properInvariant A e hA
  have hSource (u v : Fin r → RVInfinity M) : IsOpen (graphFibreSource (vfRelabeling A e) u v) := by
    rw [vfRelabeling_graph_source]
    split_ifs
    · exact (hA.clopen_fibres hv u).isOpen
    · exact isOpen_empty
  have hRange (u v : Fin r → RVInfinity M) : IsClopen (graphFibreRange (vfRelabeling A e) u v) := by
    rw [vfRelabeling_graph_range]
    split_ifs
    · exact hB.clopen_fibres hv v
    · exact isClopen_empty
  have hCov := properCovariant_of_clopen_ranges h00 hc hκ hs hv (vfRelabeling A e) hA hB
    (vfRelabeling_continuous A e) hSource hRange
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ
    (vfRelabeling A e) hCov (vfRelabeling_bijective A e) (vfRelabeling_continuous A e)

theorem vfRelabeling_derivative
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n))
    (hA : ProperInvariant S A.carrier) (p : A) :
    HasMixedVFDerivativeAt (vfRelabeling A e) p (vfReindexLinear e) := by
  obtain ⟨ρ,hρ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((hA.clopen_fibres hv p.val.2).isOpen.mem_nhds p.property)
  refine ⟨fun x => vfReindexLinear e x+0,⟨ρ,fun x hx => ⟨hρ hx,?_⟩⟩,
    hasVFDerivativeAt_affine (vfReindexLinear e) 0 p.val.1⟩
  change (x ∘ e,p.val.2)=(vfReindexLinear e x+0,p.val.2)
  rw [add_zero,vfReindexLinear_apply]

theorem vfReindexLinear_symm_comp (e : Equiv.Perm (Fin n)) :
    (vfReindexLinear (M := M) e.symm).comp (vfReindexLinear e)=LinearMap.id := by
  ext x i
  simp only [LinearMap.comp_apply,vfReindexLinear_apply,LinearMap.id_coe,id_eq,Function.comp_apply,Equiv.apply_symm_apply]

end DiamondIntegral.Section6
