import «section 3».IntegrationMixedCodes
import IntegrationSection3ACVF.CoordinateOpenToOpen
import «section 3».IntegrationBallShapes
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def integrationMixedVFIndex (r : ℕ) : Fin (1+r) := Fin.castAdd r 0

theorem integrationMixedVFCoordinate {r : ℕ} (p : Section2.Mixed M 1 r) :
    Section2.mixedTuple p (integrationMixedVFIndex r) = (p.1 0).val := by
  simp only [integrationMixedVFIndex,Section2.mixedTuple,Fin.append_left,vfValues]

def integrationMixedContext {r : ℕ} (t : Fin r → Section2.RVInfinity M) :
    CoordinateSlices.Other (integrationMixedVFIndex r) → M :=
  CoordinateSlices.tail (integrationMixedVFIndex r) (Section2.mixedTuple ((fun _ => (0 : Section2.VF M)),t))

theorem integrationMixedTail {r : ℕ} (p : Section2.Mixed M 1 r) :
    CoordinateSlices.tail (integrationMixedVFIndex r) (Section2.mixedTuple p) = integrationMixedContext p.2 := by
  funext j
  have he := j.property
  change Section2.mixedTuple p j.val = Section2.mixedTuple ((fun _ => (0 : Section2.VF M)),p.2) j.val
  revert he
  refine Fin.addCases (fun i hi => ?_) (fun i _ => ?_) j.val
  · have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
    exact (hi (congrArg (Fin.castAdd r) hi0)).elim
  · simp only [Section2.mixedTuple,Fin.append_right,rvValues]

theorem integrationMixedInsert {r : ℕ} (x : Section2.VF M) (t : Fin r → Section2.RVInfinity M) :
    CoordinateSlices.insert (integrationMixedVFIndex r) (integrationMixedContext t) x.val =
      Section2.mixedTuple ((fun _ => x),t) := by
  have he := CoordinateSlices.insert_tail (integrationMixedVFIndex r) (Section2.mixedTuple ((fun _ => x),t))
  rw [integrationMixedTail,integrationMixedVFCoordinate] at he
  exact he

/-- Fixed source and target RV labels, with the checked paper convention
that the whole VF line is also open. The iff is retained for inversion. -/
def IntegrationMixedPaperFibres {r s : ℕ} (A : Set (Section2.Mixed M 1 r))
    (f : Section2.Mixed M 1 r → Section2.Mixed M 1 s) : Prop :=
  ∀ (t : Fin r → Section2.RVInfinity M) (u : Fin s → Section2.RVInfinity M) (D : Set (Section2.VF M)),
    (∀ x ∈ D, ((fun _ => x),t) ∈ A ∧ (f ((fun _ => x),t)).2 = u) →
    (PaperBalls.IsOpenBall (Subtype.val '' D) ↔
      PaperBalls.IsOpenBall (Subtype.val '' ((fun x => (f ((fun _ => x),t)).1 0) '' D)))

theorem integrationMixedPaperFibres_of_coordinate {r s : ℕ}
    (A : Set (Section2.Mixed M 1 r)) (f : Section2.Mixed M 1 r → Section2.Mixed M 1 s)
    {W : Set (Fin (1+r) → M)} (hW : W ⊆ Section2.mixedTuple '' A)
    (h : CoordinateOpenToOpen.At W (integrationMixedRawMap A f)
      (integrationMixedVFIndex r) (integrationMixedVFIndex s)) :
    IntegrationMixedPaperFibres (Section2.mixedTuple ⁻¹' W) f := by
  intro t u D hD
  have hsub : Subtype.val '' D ⊆ CoordinateFibres.source W (integrationMixedRawMap A f)
      (integrationMixedVFIndex r) (integrationMixedVFIndex s) (integrationMixedContext t) (integrationMixedContext u) := by
    rintro x ⟨a,ha,rfl⟩
    rw [CoordinateFibres.source,Set.mem_ofPred_eq,integrationMixedInsert]
    have hAa : ((fun _ => a),t) ∈ A := by
      obtain ⟨b,hb,he⟩ := hW (hD a ha).1
      exact integrationMixedTuple_injective he ▸ hb
    refine ⟨(hD a ha).1,?_⟩
    rw [integrationMixedRawMap_on A f _ hAa,integrationMixedTail,(hD a ha).2]
  have him : CoordinateFibres.map (integrationMixedRawMap A f) (integrationMixedVFIndex r)
      (integrationMixedVFIndex s) (integrationMixedContext t) '' (Subtype.val '' D) =
      Subtype.val '' ((fun x => (f ((fun _ => x),t)).1 0) '' D) := by
    ext y
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      have hAx : ((fun _ => x),t) ∈ A := by
        obtain ⟨b,hb,he⟩ := hW (hD x hx).1
        exact integrationMixedTuple_injective he ▸ hb
      refine ⟨_,⟨x,hx,rfl⟩,?_⟩
      simp only [CoordinateFibres.map,integrationMixedInsert,integrationMixedRawMap_on A f _ hAx,
        integrationMixedVFCoordinate]
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      have hAx : ((fun _ => x),t) ∈ A := by
        obtain ⟨b,hb,he⟩ := hW (hD x hx).1
        exact integrationMixedTuple_injective he ▸ hb
      refine ⟨x.val,⟨x,hx,rfl⟩,?_⟩
      simp only [CoordinateFibres.map,integrationMixedInsert,integrationMixedRawMap_on A f _ hAx,
        integrationMixedVFCoordinate]
  simpa only [him] using h (integrationMixedContext t) (integrationMixedContext u) (Subtype.val '' D) hsub
end DiamondIntegral.Section3
