import «section 6».UnaryIndexedFamilyMaps
import «section 6».UnaryIndexedMixedFamilies
import «section 6».UncurriedFamilyMapValues

/-! Actual continuous-tail family maps at a unary mixed parameter.
The complete graph is composed through the parameter projection; no
continuity of the parameter map in the first coordinate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s m : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

def unaryIndexedParameterProjection
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S) :
    Map C (DefSet.univ (rawMixedSpace (M := M) (n+1) s) S) :=
  (unaryFamilyParameterMap η n s).comp (Map.inclusion (fun _ _ => Set.mem_univ _))

theorem unaryIndexedParameterProjection_image_good
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (F : ContinuousRVGraphTemplate (M := M) S 1 s n m)
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier)
    (hGood : ∀ p ∈ C.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ F.good) :
    ∀ z ∈ (unaryIndexedParameterProjection η C).image.carrier,
      (fun _ : Fin 1 => (z.1 0).val) ∈ F.good := by
  rintro z ⟨p,rfl⟩
  let b : B := ⟨unaryFamilyBasePoint p.val,hBase p.val p.property⟩
  change (fun _ : Fin 1 => ((unaryFamilyParameterPoint η p.val).1 0).val) ∈ F.good
  rw [unaryFamilyParameterPoint_at η p.val b rfl]
  exact hGood p.val p.property b rfl

def unaryIndexedFamilyMap
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (F : ContinuousRVGraphTemplate (M := M) S 1 s n m)
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier)
    (hGood : ∀ p ∈ C.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ F.good) : Map C (DefSet.univ (rawVFSpace (M := M) m) S) :=
  (uncurriedFamilyMap F (unaryIndexedParameterProjection η C).image
    (unaryIndexedParameterProjection_image_good η F C hBase hGood)).comp
      (unaryIndexedParameterProjection η C).toImage

theorem unaryIndexedFamilyMap_value
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (F : ContinuousRVGraphTemplate (M := M) S 1 s n m)
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier)
    (hGood : ∀ p ∈ C.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ F.good)
    (p : C) (b : B) (hb : unaryFamilyBasePoint p.val=b.val) :
    (unaryIndexedFamilyMap η F C hBase hGood p).val=
      F.value _ (hGood p.val p.property b hb) (p.val.2 ∘ Fin.natAdd r) (Fin.tail p.val.1) := by
  have hRel : uncurriedFamilyRelation F (unaryIndexedParameterProjection η C).image
      ((unaryIndexedParameterProjection η C).toImage p).val
      (unaryIndexedFamilyMap η F C hBase hGood p).val := by
    change uncurriedFamilyRelation F _ _
      (uncurriedFamilyMap F _ (unaryIndexedParameterProjection_image_good η F C hBase hGood) _).val
    unfold uncurriedFamilyMap
    exact Map.ofFunctionalRelation_graph _ _ _ _ _
  have hRaw := hRel.2
  change Sum.elim (fun _ : Fin 1 => ((unaryFamilyParameterPoint η p.val).1 0).val)
    (Sum.elim (rvValues (unaryFamilyParameterPoint η p.val).2)
      (Sum.elim (vfValues (Fin.tail (unaryFamilyParameterPoint η p.val).1))
        (vfValues (unaryIndexedFamilyMap η F C hBase hGood p).val))) ∈ F.graph at hRaw
  rw [unaryFamilyParameterPoint_at η p.val b hb] at hRaw
  exact ((F.value_graph_at _ (hGood p.val p.property b hb) (p.val.2 ∘ Fin.natAdd r)
    (Fin.tail p.val.1) (unaryIndexedFamilyMap η F C hBase hGood p).val).mp hRaw).symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unaryIndexedFamilyMap_tail_continuous
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (F : ContinuousRVGraphTemplate (M := M) S 1 s n 1)
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier)
    (hGood : ∀ p ∈ C.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ F.good)
    (u : Fin (r+s) → RVInfinity M) (a : VF M) :
    Continuous (focusTailMap (unaryIndexedFamilyMap η F C hBase hGood) u a) := by
  by_cases hNonempty : Nonempty (focusTailDomain C u a)
  · obtain ⟨p⟩ := hNonempty
    let b : B := ⟨unaryFamilyBasePoint (Fin.cons a p.val,u),hBase _ p.property⟩
    have hPoint (x : Fin n → VF M) : unaryFamilyBasePoint (Fin.cons a x,u)=b.val := rfl
    have ha := hGood (Fin.cons a p.val,u) p.property b (hPoint p.val)
    have he : focusTailMap (unaryIndexedFamilyMap η F C hBase hGood) u a=
        (fun x : focusTailDomain C u a => F.value _ ha (u ∘ Fin.natAdd r) x.val) := by
      funext x
      change (unaryIndexedFamilyMap η F C hBase hGood ⟨(Fin.cons a x.val,u),x.property⟩).val=_
      rw [unaryIndexedFamilyMap_value η F C hBase hGood _ b (hPoint x.val)]
      rfl
    rw [he]
    exact (F.value_continuous hv _ ha (u ∘ Fin.natAdd r)).comp continuous_subtype_val
  · have he : focusTailMap (unaryIndexedFamilyMap η F C hBase hGood) u a=
        (fun _ : focusTailDomain C u a => (0 : Fin 1 → VF M)) := by
      funext x
      exact (hNonempty ⟨x⟩).elim
    rw [he]
    exact continuous_const

end DiamondIntegral.Section6
