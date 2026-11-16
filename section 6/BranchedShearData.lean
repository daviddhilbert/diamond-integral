import «section 6».OpenLabelShearContractions
import «section 6».ContinuousRVFamilyMaps
import «section 6».ScalarIndicatorMaps
import «section 6».RVLabelSelection

/-! Definable continuous charts for a relatively unary contraction.
A source indicator selects exactly one output RV tuple. The offset
depends only on inactive coordinates. The selected graph is an actual
definable set bijective with the original source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure BranchedShearData (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) where
  arity : ℕ
  indicator : (Fin (r+arity) → RVInfinity M) → (Fin (n+1) → VF M) → Fin 1 → VF M
  offset : (Fin (r+arity) → RVInfinity M) → (Fin n → VF M) → Fin 1 → VF M
  indicator_definable : S.Definable LRV (rvVFGraph indicator)
  offset_definable : S.Definable LRV (rvVFGraph offset)
  indicator_continuous : ∀ w,Continuous (indicator w)
  offset_continuous : ∀ w,Continuous (offset w)
  labels : Fin r → Fin arity
  labels_injective : Function.Injective labels
  leading : Fin arity
  binary : ∀ w x,indicator w x 0=0 ∨ indicator w x 0=1
  source : ∀ x u,(x,u) ∈ A.carrier ↔ ∃ v,indicator (Fin.append u v) x 0=1
  unique : ∀ x u v w,indicator (Fin.append u v) x 0=1 → indicator (Fin.append u w) x 0=1 → v=w
  retained : ∀ x u v,indicator (Fin.append u v) x 0=1 → v ∘ labels=u
  nonzero : ∀ x u v,indicator (Fin.append u v) x 0=1 → ∀ i,(v i).val ≠ iRVZero
  leading_value : ∀ x u v,indicator (Fin.append u v) x 0=1 →
    rv M (x (Fin.last n)+offset (Fin.append u v) (Fin.init x) 0)=v leading
  full_disc : ∀ x u v,indicator (Fin.append u v) x 0=1 → ∀ d : VF M,rv M d=v leading →
    indicator (Fin.append u v)
      (Function.update x (Fin.last n) (d-offset (Fin.append u v) (Fin.init x) 0)) 0=1

namespace BranchedShearData
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def indicatorMap (T : BranchedShearData (G := G) A) :
    Map (DefSet.univ (rawMixedSpace (M := M) (n+1) (r+T.arity)) S) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  rvFamilyMap _ T.indicator T.indicator_definable

def domain (T : BranchedShearData (G := G) A) := scalarLevelOne T.indicatorMap

theorem mem_domain (T : BranchedShearData (G := G) A) (p : Mixed M (n+1) (r+T.arity)) :
    p ∈ T.domain.carrier ↔ T.indicator p.2 p.1 0=1 := by
  change p ∈ (scalarLevelOne T.indicatorMap).carrier ↔ _
  rw [mem_scalarLevelOne,totalFocusFibre_at _ p.2 p.1 (Set.mem_univ _)]
  exact and_iff_right (Set.mem_univ _)

def sourceMap (T : BranchedShearData (G := G) A) : Map T.domain A := by
  refine (selectRVLabelsMap T.domain (Fin.castAdd T.arity)).corestrict ?_
  intro p
  have h := (T.mem_domain p.val).mp p.property
  apply (T.source p.val.1 (p.val.2 ∘ Fin.castAdd T.arity)).mpr
  refine ⟨p.val.2 ∘ Fin.natAdd r,?_⟩
  simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using h

theorem sourceMap_value (T : BranchedShearData (G := G) A) (p : T.domain) :
    (T.sourceMap p).val=(p.val.1,p.val.2 ∘ Fin.castAdd T.arity) := rfl

theorem sourceMap_bijective (T : BranchedShearData (G := G) A) : Function.Bijective T.sourceMap := by
  constructor
  · intro p q he
    have hVF : p.val.1=q.val.1 := congrArg (fun z : A => z.val.1) he
    have hOld : p.val.2 ∘ Fin.castAdd T.arity=q.val.2 ∘ Fin.castAdd T.arity :=
      congrArg (fun z : A => z.val.2) he
    have hP : T.indicator (Fin.append (p.val.2 ∘ Fin.castAdd T.arity) (p.val.2 ∘ Fin.natAdd r)) p.val.1 0=1 := by
      simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using (T.mem_domain p.val).mp p.property
    have hQ : T.indicator (Fin.append (p.val.2 ∘ Fin.castAdd T.arity) (q.val.2 ∘ Fin.natAdd r)) p.val.1 0=1 := by
      rw [hOld,hVF]
      simpa only [Function.comp_def,Fin.append_castAdd_natAdd] using (T.mem_domain q.val).mp q.property
    have hNew := T.unique _ _ _ _ hP hQ
    have hTags : p.val.2=q.val.2 := by
      calc
        _=Fin.append (p.val.2 ∘ Fin.castAdd T.arity) (p.val.2 ∘ Fin.natAdd r) := Fin.append_castAdd_natAdd.symm
        _=Fin.append (q.val.2 ∘ Fin.castAdd T.arity) (q.val.2 ∘ Fin.natAdd r) := congrArg₂ Fin.append hOld hNew
        _=_ := Fin.append_castAdd_natAdd
    exact Subtype.ext (Prod.ext hVF hTags)
  · intro p
    obtain ⟨v,hv⟩ := (T.source p.val.1 p.val.2).mp p.property
    let q : T.domain := ⟨(p.val.1,Fin.append p.val.2 v),(T.mem_domain _).mpr hv⟩
    refine ⟨q,Subtype.ext ?_⟩
    rw [T.sourceMap_value]
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.append_left p.val.2 v i

def selectedPoint (T : BranchedShearData (G := G) A) : Map A T.domain := T.sourceMap.inverse T.sourceMap_bijective

theorem selectedPoint_source (T : BranchedShearData (G := G) A) (p : A) : T.sourceMap (T.selectedPoint p)=p :=
  Map.apply_inverse _ _ p

theorem selectedPoint_vf (T : BranchedShearData (G := G) A) (p : A) : (T.selectedPoint p).val.1=p.val.1 :=
  congrArg (fun q : A => q.val.1) (T.selectedPoint_source p)

end BranchedShearData
end DiamondIntegral.Section6
