import «section 6».FrozenChoiceFusion
import «section 6».DoublyBoundedPullbackInvariance

/-! The actual first-coordinate projection supplies the unary base
of the dimension induction. Its complete graph, bounds, pullback and
taggedness remain over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def vfHeadProjection (H : DefSet (rawMixedSpace (M := M) (n+1) r) S) :
    Map H (DefSet.univ (rawMixedSpace (M := M) 1 r) S) :=
  (unaryFamilyBaseMap S n r 0).comp (Map.inclusion (fun _ _ => Set.mem_univ _))

theorem vfHeadProjection_value (H : DefSet (rawMixedSpace (M := M) (n+1) r) S) (p : H) :
    (vfHeadProjection H p).val=(fun _ : Fin 1 => p.val.1 0,p.val.2) := by
  apply Prod.ext
  · rfl
  · funext i
    change p.val.2 (Fin.castAdd 0 i)=p.val.2 i
    congr 1

theorem vfHeadProjection_doublyBounded (H : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hH : VFDoublyBounded H.carrier) : VFDoublyBounded (vfHeadProjection H).image.carrier := by
  obtain ⟨γ,hγ⟩ := hH
  refine ⟨γ,?_⟩
  rintro z ⟨p,rfl⟩ i
  change γ⁻¹.val ≤ vfValue ((vfHeadProjection H p).val.1 i) ∧
    vfValue ((vfHeadProjection H p).val.1 i) ≤ γ.val
  rw [vfHeadProjection_value]
  exact hγ p.val p.property 0

theorem vfHeadProjection_rvBounded (H : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hH : RVSupportDoublyBounded H.carrier) : RVSupportDoublyBounded (vfHeadProjection H).image.carrier := by
  obtain ⟨γ,hγ⟩ := hH
  refine ⟨γ,?_⟩
  rintro z ⟨p,rfl⟩ i
  change γ⁻¹.val ≤ Values.vrv ((vfHeadProjection H p).val.2 i) ∧
    Values.vrv ((vfHeadProjection H p).val.2 i) ≤ γ.val
  rw [vfHeadProjection_value]
  exact hγ p.val p.property i

theorem vfHeadProjection_rvPullback (H : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hH : IsRVPullback H.carrier) : IsRVPullback (vfHeadProjection H).image.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro z hz
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ z).mp hz
  obtain ⟨a,rfl⟩ := hp
  change tupleRV M (vfHeadProjection H a).val.1=tupleRV M z.1 at hVF
  change (vfHeadProjection H a).val.2=z.2 at hRV
  rw [vfHeadProjection_value] at hVF hRV
  let x : Mixed M (n+1) r := (Function.update a.val.1 0 (z.1 0),z.2)
  have hxRV : tupleRV M a.val.1=tupleRV M x.1 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change rv M (a.val.1 0)=rv M (Function.update a.val.1 0 (z.1 0) 0)
      rw [Function.update_self]
      exact congrFun hVF 0
    · change rv M (a.val.1 j.succ)=rv M (Function.update a.val.1 0 (z.1 0) j.succ)
      rw [Function.update_of_ne (Fin.succ_ne_zero j)]
  have hx : x ∈ H.carrier := rvPullback_mem_of_sameRV hH a.property hxRV hRV
  refine ⟨⟨x,hx⟩,?_⟩
  change (vfHeadProjection H ⟨x,hx⟩).val=z
  rw [vfHeadProjection_value]
  apply Prod.ext
  · funext i
    fin_cases i
    change Function.update a.val.1 0 (z.1 0) 0=z.1 0
    rw [Function.update_self]
  · rfl

theorem vfHeadProjection_tagged (H : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hH : ∀ p ∈ H.carrier,∀ z ∈ H.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1) :
    ∀ p ∈ (vfHeadProjection H).image.carrier,∀ z ∈ (vfHeadProjection H).image.carrier,
      p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
  rintro p ⟨a,rfl⟩ z ⟨b,rfl⟩ hTags
  change (vfHeadProjection H a).val.2=(vfHeadProjection H b).val.2 at hTags
  change tupleRV M (vfHeadProjection H a).val.1=tupleRV M (vfHeadProjection H b).val.1
  rw [vfHeadProjection_value,vfHeadProjection_value] at hTags ⊢
  funext i
  exact congrFun (hH a.val a.property b.val b.property hTags) 0

def headPreparationContext (H : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hH : ProperInvariant S H.carrier) (hD : VFDoublyBounded H.carrier) (hRP : IsRVPullback H.carrier)
    (hTag : ∀ p ∈ H.carrier,∀ z ∈ H.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1) :
    UnaryPreparationContext (vfHeadProjection H).image (0 : Fin (n+1)) where
  arity := r
  source := H
  labels := id
  projection := (vfHeadProjection H).toImage
  projection_value p := vfHeadProjection_value H p
  proper := hH
  doublyBounded := hD
  pullback := hRP
  tagged := hTag

end DiamondIntegral.Section6
