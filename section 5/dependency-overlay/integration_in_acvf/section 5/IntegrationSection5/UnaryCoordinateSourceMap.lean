import IntegrationSection5.ActiveUnaryProjection
import IntegrationSection5.GammaGraphOperations

/-! Actual source projections to a unary VF presentation, with their full
original-base graphs and uniqueness at RV arity zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ}

def unaryCoordinateSourceMap (A : DefSet (M := M) S 1 0) (H : DefSet (M := M) S n m)
    (i : Fin n) (hHA : ∀ p ∈ carrier H, activeUnaryProjection i Fin.elim0 p ∈ carrier A) : Map H A :=
  Map.mk (fun p => ⟨activeUnaryProjection i Fin.elim0 p.val,hHA p.val p.property⟩)
    (Map.graph_definable (activeUnaryProjectionMap i Fin.elim0 H))

theorem unary_zeroRV_ext {A : DefSet (M := M) S 1 0} {a b : A}
    (h : vfAt a.val 0 = vfAt b.val 0) : a = b := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · funext j
    fin_cases j
    exact h
  · funext j
    exact j.elim0

theorem gamma_unaryCoordinateSourceMap (A : DefSet (M := M) S 1 0) (H : DefSet (M := M) S n m)
    (i : Fin n) (hHA : ∀ p ∈ carrier H, activeUnaryProjection i Fin.elim0 p ∈ carrier A)
    (hH : GammaSetDefinable G (carrier H)) :
    GammaGraphDefinable G (pointMapGraph (unaryCoordinateSourceMap A H i hHA)) := by
  let X := PresentedSet.univ (pointSpace (M := M) n m) G.real
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hH
    ((gammaLogicInput G).real_map_graph (activeUnaryProjectionMap i Fin.elim0 X)))
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    exact ⟨⟨p,hp⟩,rfl,(congrArg (activeUnaryProjection i Fin.elim0) ha).symm.trans hq⟩
  · rintro ⟨a,rfl,hq⟩
    exact ⟨a.property,⟨a.val,Set.mem_univ _⟩,rfl,hq⟩

end IntegrationInACVF.Section5
