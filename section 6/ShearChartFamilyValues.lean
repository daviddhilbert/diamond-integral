import «section 6».ContinuousGraphShearDisplacements
import «section 6».GraphChartIndicators

/-! Exact values of the two chart families extracted from an actual
stable shear: the indicator is its source graph condition, and the
inactive displacement is the actual output-minus-input coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} {B : DefSet (rawMixedSpace (M := M) (n+1) s) S}

theorem graphChartSourceIndicator_eq_one_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (w : Fin (r+s) → RVInfinity M) (x : Fin (n+1) → VF M) :
    totalFocusFibre (graphChartSourceIndicator hc f) w x 0=1 ↔
      x ∈ graphFibreSource f (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r) := by
  rw [graphChartSourceIndicator_value]
  by_cases h : x ∈ graphFibreSource f (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r) <;> simp [h]

theorem graphChartSourceIndicator_family_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) :
    S.Definable LRV (rvVFGraph (totalFocusFibre (graphChartSourceIndicator hc f))) := by
  let χ := graphChartSourceIndicator hc f
  rw [rvVFGraph_eq_functionFamilyGraph (totalFocusFamilyCode χ) (totalFocusFibre χ) (totalFocusFamilyCode_at χ)]
  exact rvFunctionFamilyGraph_definable _ (totalFocusFamilyCode_definable χ)

theorem graphShearBaseDisplacement_at_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (hStable : SameLabelShearDisplacement f (Fin.last n))
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (x y : Fin (n+1) → VF M) (hGraph : graphFibre f u v x y) :
    totalFocusFibre (graphShearBaseDisplacement hc f hStable) (Fin.append u v) (Fin.init x) 0=
      y (Fin.last n)-x (Fin.last n) := by
  obtain ⟨p,hp,hfp⟩ := hGraph
  let q := graft hc (rvProjection f) p
  let C := (vfDropLast (graphChartDomain hc f)).image
  let δ := graphShearBaseDisplacement hc f hStable
  have hBase : (Fin.init q.val.1,q.val.2) ∈ C.carrier := ⟨q,rfl⟩
  have hT : totalFocusFibre δ q.val.2 (Fin.init q.val.1) 0=
      (δ ((vfDropLast (graphChartDomain hc f)).toImage q)).val 0 := by
    rw [totalFocusFibre_at δ q.val.2 (Fin.init q.val.1) hBase]
    rfl
  have hD := congrArg (fun z : DefSet.univ (rawVFSpace (M := M) 1) S => z.val 0)
    (graphShearBaseDisplacement_factor hc f hStable q)
  have h := hT.trans hD
  change totalFocusFibre δ q.val.2 (Fin.init q.val.1) 0=
    (graphShearDisplacementMap hc f (graft hc (rvProjection f) p)).val 0 at h
  rw [graphShearDisplacementMap_graft] at h
  have hInput := congrArg Prod.snd hp
  have hOutput := congrArg Prod.snd hfp
  have hXVF := congrArg Prod.fst hp
  have hYVF := congrArg Prod.fst hfp
  have hQTags : q.val.2=Fin.append u v := by
    change Fin.append p.val.2 (rvProjection f p).val.2=Fin.append u v
    rw [rvProjection_apply,hInput,hOutput]
  have hQVF : q.val.1=x := hXVF
  rw [hQTags,hQVF,hYVF,hXVF] at h
  exact h

theorem graphShearBaseDisplacement_on_source
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (hStable : SameLabelShearDisplacement f (Fin.last n)) (p : A) :
    totalFocusFibre (graphShearBaseDisplacement hc f hStable) (Fin.append p.val.2 (f p).val.2) (Fin.init p.val.1) 0=
      (f p).val.1 (Fin.last n)-p.val.1 (Fin.last n) :=
  graphShearBaseDisplacement_at_graph hc f hStable _ _ _ _ ⟨p,rfl,rfl⟩

end DiamondIntegral.Section6
