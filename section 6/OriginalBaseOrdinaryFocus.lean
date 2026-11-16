import «section 6».OrdinaryMatchingMaps
import «section 6».UnaryCentripetalExistence

/-! Full original-base scalar graphs of the actual ordinary unary
foci, with independence from the VF input and the prescribed leading
term. Internal code parameters are eliminated before forming the map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r} {j : Fin r}
namespace OriginalBaseOrdinaryFocus
variable (D : SpecialTransformations.Section5.Focus A 0 j)

def active (hc : CanonicalStructure.IsCanonical (M := M))
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D) :
    DefSet (rawMixedSpace (M := M) 1 r) S :=
  ⟨SpecialTransformations.Section5.carrier A ∩ D.locus,ordinary_named_gamma_set_definable hc _
    ((SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)).inter hA hD.1)⟩

def mixedMap (hc : CanonicalStructure.IsCanonical (M := M))
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D) :
    Map (active D hc hA hD) (DefSet.univ (rawMixedSpace (M := M) 1 0) S) where
  toFun p := ⟨(fun _ : Fin 1 => D.center p.val,Fin.elim0),Set.mem_univ _⟩
  graph_definable := (ordinary_named_gamma_graph_definable hc _ hD.2).congr
    (rawMixedSpace (M := M) 1 r) (rawMixedSpace (M := M) 1 0) (by
      intro p q
      constructor
      · rintro ⟨hp,hc⟩
        refine ⟨⟨p,hp⟩,rfl,Prod.ext ?_ ?_⟩
        · funext i
          fin_cases i
          exact hc.symm
        · exact Subsingleton.elim _ _
      · rintro ⟨p,rfl,he⟩
        exact ⟨p.property,(congrArg (fun z : Mixed M 1 0 => z.1 0) he).symm⟩)

def scalarMap (hc : CanonicalStructure.IsCanonical (M := M))
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D) :
    Map (active D hc hA hD) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (Map.fst (rawVFSpace (M := M) 1) (rawRVSpace (M := M) 0) S
    (DefSet.univ (rawMixedSpace (M := M) 1 0) S)).comp (mixedMap D hc hA hD)

theorem scalarMap_value (hc : CanonicalStructure.IsCanonical (M := M))
    (hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      (SpecialTransformations.Section5.carrier A))
    (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D)
    (p : active D hc hA hD) : (scalarMap D hc hA hD p).val 0=D.center p.val := rfl

theorem center_same_labels (p q : Mixed M 1 r)
    (hp : p ∈ SpecialTransformations.Section5.carrier A ∩ D.locus)
    (hq : q ∈ SpecialTransformations.Section5.carrier A ∩ D.locus) (hu : p.2=q.2) :
    D.center p=D.center q := by
  apply D.independent p hp q hq
  apply Prod.ext
  · funext i
    fin_cases i
    change Function.update p.1 (0 : Fin 1) (0 : VF M) (0 : Fin 1)=
      Function.update q.1 (0 : Fin 1) (0 : VF M) (0 : Fin 1)
    rw [Function.update_self,Function.update_self]
  · exact hu

theorem center_leading_term (p : Mixed M 1 r)
    (hp : p ∈ SpecialTransformations.Section5.carrier A ∩ D.locus) :
    rv M (D.center p)=rv M (p.1 0) := by
  exact D.toFocusGeometry.center_sameRV p hp

end OriginalBaseOrdinaryFocus
end DiamondIntegral.Section6
