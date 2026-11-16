import «section 6».FullFocusProtectedRealizations
import «section 6».ProtectedFocusFreezing

/-! Joint focus graphs before the continuity repair: continuity is
required on each fibre of the first VF coordinate. The target is a
different coordinate. Actual freezing preserves target independence
and leading terms and checks every current protected product domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure TailContinuousFullFocusGraphData (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) where
  coordinate : Fin (n+1)
  notHead : coordinate ≠ 0
  activeTags : DefSet (rawRVSpace (M := M) r) S
  map : Map (focusActive A activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)
  independent : ∀ p q : focusActive A activeTags,p.val.2=q.val.2 →
    (∀ i ≠ coordinate,p.val.1 i=q.val.1 i) → (map p).val 0=(map q).val 0
  proper : ProperInvariant S A.carrier
  doublyBounded : VFDoublyBounded A.carrier
  tagged : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1
  continuousTail : ∀ u a,Continuous (focusTailMap map u a)
  leadingTerm : ∀ p : focusActive A activeTags,rv M ((map p).val 0)=rv M (p.val.1 coordinate)

namespace TailContinuousFullFocusGraphData
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def frozenFullGraph
    (F : TailContinuousFullFocusGraphData (G := G) A)
    (D : FMT.FocusFreezingData (focusActive A F.activeTags))
    (hCont : ∀ u,Continuous (FMT.focusFibre (D.frozenMap F.map) u)) :
    FullFocusGraphData (G := G) A := by
  let q (p : focusActive A F.activeTags) := FMT.mixedFamilyFreeze D.balls D.centers 0 p.val
  have hq (p : focusActive A F.activeTags) : q p ∈ (focusActive A F.activeTags).carrier :=
    FMT.mixedFamilyFreeze_mapsTo D.balls D.centers 0 _ D.separated D.product_domain p.property
  refine {
    coordinate := F.coordinate
    activeTags := F.activeTags
    map := D.frozenMap F.map
    independent := ?_
    proper := F.proper
    doublyBounded := F.doublyBounded
    tagged := F.tagged
    continuous := hCont
    leadingTerm := ?_ }
  · intro p t hTags hOther
    change (F.map ⟨q p,hq p⟩).val 0=(F.map ⟨q t,hq t⟩).val 0
    apply F.independent ⟨q p,hq p⟩ ⟨q t,hq t⟩ hTags
    intro i hi
    by_cases hi0 : i=0
    · subst i
      change FMT.vfFamilyFreeze D.balls D.centers (p.val.1 0)=
        FMT.vfFamilyFreeze D.balls D.centers (t.val.1 0)
      exact congrArg _ (hOther 0 F.notHead.symm)
    · simpa only [q,FMT.mixedFamilyFreeze,Function.update_of_ne hi0] using hOther i hi
  · intro p
    change rv M ((F.map ⟨q p,hq p⟩).val 0)=rv M (p.val.1 F.coordinate)
    have hLead := F.leadingTerm ⟨q p,hq p⟩
    have hCoord : (q p).1 F.coordinate=p.val.1 F.coordinate :=
      Function.update_of_ne F.notHead _ _
    exact hLead.trans (congrArg (rv M) hCoord)

theorem exists_frozen_full_graph
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (F : TailContinuousFullFocusGraphData (G := G) A)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hP : ∀ i,ProperInvariant S (P i).carrier) :
    ∃ D : FMT.FocusFreezingData (focusActive A F.activeTags),
      (∀ u,Continuous (FMT.focusFibre (D.frozenMap F.map) u)) ∧
      (∀ E : D.balls,FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall E.val) (D.centers E) 0) ∧
      ∀ i,∀ E : D.balls,FMT.CoordinateProductDomain (P i).carrier (FMT.vfOpenBall E.val) (D.centers E) 0 := by
  let H : Fin (k+1) → Set (Mixed M (n+1) r) := Fin.cons A.carrier (fun i => (P i).carrier)
  have hH : ∀ i,ProperInvariant S (H i) := Fin.cases F.proper hP
  obtain ⟨δ,hδ,hδ1,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  have hActive (u) : AlphaInvariant (fun _ => δ) (vfFibre (focusActive A F.activeTags).carrier u) := by
    intro a b hab
    exact and_congr (hInv 0 u a b hab) Iff.rfl
  obtain ⟨s,hs0,hsdef,hδs⟩ := exists_named_vf_above_radius Valued.v hv hc h00
    V S hV hVS hSV hnt δ hδ1 hδ
  let Q : Fin (k+1) → DefSet (rawMixedSpace (M := M) (n+1) r) S := Fin.cons A P
  have hQ : ∀ i u,AlphaInvariant (fun _ => δ) (vfFibre (Q i).carrier u) :=
    Fin.cases (hInv 0) (fun i => hInv i.succ)
  obtain ⟨D,hCont,hProd⟩ := FMT.exists_continuous_focus_freezing_with_domains h00 hc hκ hs hsmall hv
    δ hActive s hs0 hsdef hδs.le F.map F.continuousTail Q hQ (0 : Fin (n+1))
  exact ⟨D,hCont,hProd 0,fun i => hProd i.succ⟩

end TailContinuousFullFocusGraphData
end DiamondIntegral.Section6
