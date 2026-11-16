import «section 6».SurjectiveMapDescent
import «section 6».VFProjection

/-! Descend the actual centripetal focus through the coordinate being
released. The complete graph and continuity remain over the original
base; every protected focus-graph piece on the projected domain is
proper invariant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem focusActive_properInvariant
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (U : DefSet (rawRVSpace (M := M) r) S) : ProperInvariant S (focusActive A U).carrier := by
  have hsub : (focusActive A U).carrier ⊆ A.carrier := fun _ h => h.1
  refine ⟨(focusActive A U).definable,hA.vfBounded.mono hsub,hA.rvBounded.mono hsub,fun u => ?_⟩
  obtain ⟨α,hα,hInv⟩ := hA.radii u
  refine ⟨α,hα,fun a b hab => ?_⟩
  exact and_congr (hInv a b hab) Iff.rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace CentripetalData

variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def focusProjectionDomain (D : CentripetalData (G := G) A) :
    DefSet (rawMixedSpace (M := M) n r) S := (vfDropLast (focusActive A D.activeTags)).image

theorem focusProjection_compatible (D : CentripetalData (G := G) A)
    (hj : D.coordinate = Fin.last n) :
    ∀ a b : focusActive A D.activeTags,
      (vfDropLast (focusActive A D.activeTags)).toImage a =
        (vfDropLast (focusActive A D.activeTags)).toImage b → D.focusMap a = D.focusMap b := by
  intro a b he
  have hinit : Fin.init a.val.1 = Fin.init b.val.1 := congrArg (fun p => p.val.1) he
  have htags : a.val.2 = b.val.2 := congrArg (fun p => p.val.2) he
  have herase : Function.update a.val.1 D.coordinate 0 = Function.update b.val.1 D.coordinate 0 := by
    rw [hj]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.update_self]
    · simp only [Function.update_of_ne (Fin.castSucc_ne_last j)]
      exact congrFun hinit j
  apply Subtype.ext
  funext i
  fin_cases i
  change (D.focusMap a).val 0 = (D.focusMap b).val 0
  rw [D.focusMap_eq a,D.focusMap_eq b,herase,htags]

def projectedFocusMap (D : CentripetalData (G := G) A) (hj : D.coordinate = Fin.last n) :
    Map D.focusProjectionDomain (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  descendSurjectiveMap (vfDropLast (focusActive A D.activeTags)).toImage
    (map_toImage_surjective _) D.focusMap (D.focusProjection_compatible hj)

theorem focusProjectionDomain_properInvariant (D : CentripetalData (G := G) A) :
    ProperInvariant S D.focusProjectionDomain.carrier :=
  vfDropLast_image_properInvariant (focusActive_properInvariant A D.sourceProper D.activeTags)

theorem projectedFocusMap_value (D : CentripetalData (G := G) A) (hj : D.coordinate = Fin.last n)
    (p : D.focusProjectionDomain) :
    (D.projectedFocusMap hj p).val 0 = D.focus (Fin.snoc p.val.1 0) p.val.2 := by
  obtain ⟨q,hq⟩ := p.property
  have hp : (vfDropLast (focusActive A D.activeTags)).toImage q = p := Subtype.ext hq
  rw [← hp]
  have hf := descendSurjectiveMap_factor (vfDropLast (focusActive A D.activeTags)).toImage
    (map_toImage_surjective _) D.focusMap (D.focusProjection_compatible hj) q
  have he : Function.update q.val.1 D.coordinate 0 = Fin.snoc (Fin.init q.val.1) 0 := by
    rw [hj]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.update_self,Fin.snoc_last]
    · simp only [Function.update_of_ne (Fin.castSucc_ne_last j),Fin.snoc_castSucc,Fin.init]
  calc
    _ = (D.focusMap q).val 0 := congrArg
      (fun z : DefSet.univ (rawVFSpace (M := M) 1) S => z.val 0) hf
    _ = D.focus (Function.update q.val.1 D.coordinate 0) q.val.2 := D.focusMap_eq q
    _ = D.focus (Fin.snoc (Fin.init q.val.1) 0) q.val.2 := congrArg (fun x => D.focus x q.val.2) he
    _ = _ := rfl

theorem projectedFocusMap_continuous
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) A) (hj : D.coordinate = Fin.last n)
    (u : Fin r → RVInfinity M) : Continuous (FMT.focusFibre (D.projectedFocusMap hj) u) := by
  let F (b : Fin n → VF M) := D.focus (Fin.snoc b 0) u
  have hF : ContinuousOn F (vfFibre D.focusProjectionDomain.carrier u) := by
    intro b hb
    obtain ⟨q,hq⟩ := hb
    have hinit : Fin.init q.val.1 = b := congrArg Prod.fst hq
    have htags : q.val.2 = u := congrArg Prod.snd hq
    have hu : u ∈ D.activeTags.carrier := htags ▸ q.property.2
    let sectionPoint (c : Fin n → VF M) : Fin (n+1) → VF M := Fin.snoc c (q.val.1 (Fin.last n))
    have hsec : Continuous sectionPoint := by
      apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [sectionPoint,Fin.snoc_last] using
          (continuous_const : Continuous (fun _ : Fin n → VF M => q.val.1 (Fin.last n)))
      · simpa only [sectionPoint,Fin.snoc_castSucc] using
          (continuous_apply j : Continuous (fun c : Fin n → VF M => c j))
    have hqb : sectionPoint b = q.val.1 := by
      change Fin.snoc b (q.val.1 (Fin.last n)) = q.val.1
      rw [← hinit,Fin.snoc_init_self]
    have hmem : sectionPoint b ∈ vfFibre A.carrier u := by
      rw [hqb,← htags]
      exact q.property.1
    have hcont : ContinuousAt (fun x => D.focus (Function.update x D.coordinate 0) u) (sectionPoint b) :=
      (D.continuous u hu).continuousAt ((D.sourceProper.clopen_fibres hv u).isOpen.mem_nhds hmem)
    have hcomp : ContinuousAt ((fun x => D.focus (Function.update x D.coordinate 0) u) ∘ sectionPoint) b :=
      ContinuousAt.comp (f := sectionPoint) (x := b) hcont hsec.continuousAt
    have he : ((fun x => D.focus (Function.update x D.coordinate 0) u) ∘ sectionPoint) = F := by
      funext c
      apply congrArg (fun x => D.focus x u)
      rw [hj]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [sectionPoint,Function.update_self,Fin.snoc_last]
      · simp only [sectionPoint,Function.update_of_ne (Fin.castSucc_ne_last j),Fin.snoc_castSucc]
    rw [he] at hcomp
    exact hcomp.continuousWithinAt
  convert hF.domRestrict using 1
  funext p
  exact D.projectedFocusMap_value hj ⟨(p.val,u),p.property⟩

theorem projected_protected_piece_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) A) (hj : D.coordinate = Fin.last n)
    (P : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hP : ProperInvariant S P.carrier) :
    ProperInvariant S (projectedFocusPiece (D.projectedFocusMap hj) P).carrier :=
  projectedFocusPiece_properInvariant h00 hc hκ hs hv (D.projectedFocusMap hj)
    D.focusProjectionDomain_properInvariant P hP (D.projectedFocusMap_continuous hv hj)

end CentripetalData
end DiamondIntegral.Section6
