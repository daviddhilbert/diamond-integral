import «section 6».DefinableGraphChartFamilies
import «section 6».ScalarIndicatorMaps

/-! The source condition of every fixed-label graph is an actual
original-base definable scalar indicator, continuous for a proper
covariant homeomorphism. It can share the same parameter repair as
the scalar VF charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

def graphChartSourceIndicator (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) :
    Map (DefSet.univ (rawMixedSpace (M := M) n (r+s)) S) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  scalarIndicatorMap _ (graphChartDomain hc f)

theorem graphChartSourceIndicator_value (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (w : Fin (r+s) → RVInfinity M) (x : Fin n → VF M) :
    totalFocusFibre (graphChartSourceIndicator hc f) w x=
      fun _ => if x ∈ graphFibreSource f (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r) then 1 else 0 := by
  rw [totalFocusFibre_at _ w x (Set.mem_univ _)]
  funext i
  have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change (if (x,w) ∈ (graphChartDomain hc f).carrier then (1 : VF M) else 0)=_
  have hMem : (x,w) ∈ (graphChartDomain hc f).carrier ↔
      x ∈ graphFibreSource f (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r) :=
    Set.ext_iff.mp (graphChartDomain_fibre hc f w) x
  simp only [hMem]

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem graphChartSourceIndicator_continuous
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hF : ProperCovariantHomeomorphism f) (w : Fin (r+s) → RVInfinity M) :
    Continuous (totalFocusFibre (graphChartSourceIndicator hc f) w) := by
  have he : totalFocusFibre (graphChartSourceIndicator hc f) w=
      fun x => fun _ : Fin 1 => if x ∈ graphFibreSource f (w ∘ Fin.castAdd s) (w ∘ Fin.natAdd r) then 1 else 0 :=
    funext (graphChartSourceIndicator_value hc f w)
  rw [he]
  exact continuous_pi (fun _ => hF.graphSourceIndicator_continuous hv _ _)

end DiamondIntegral.Section6
