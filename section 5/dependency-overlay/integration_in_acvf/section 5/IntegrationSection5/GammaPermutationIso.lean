import IntegrationSection5.VFPermutation
import IntegrationSection5.GammaIsoCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m : ℕ}

def vfPermutedSet (A : Set (Point (M := M) n m)) (σ : Equiv.Perm (Fin n)) :
    Set (Point (M := M) n m) := (vfPermutation σ) '' A

def gammaPermutationIso (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable G A)
    (σ : Equiv.Perm (Fin n)) : GammaIso G A (vfPermutedSet A σ) where
  equiv := Equiv.ofBijective (fun a => ⟨vfPermutation σ a.val,⟨a.val,a.property,rfl⟩⟩)
    ⟨fun a b he => Subtype.ext (vfPermutation_injective σ (congrArg Subtype.val he)),
      by rintro ⟨q,p,hp,hq⟩; exact ⟨⟨p,hp⟩,Subtype.ext hq⟩⟩
  graph := by
    let X := PresentedSet.univ (pointSpace (M := M) n m) G.real
    apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hA
      ((gammaLogicInput G).real_map_graph (vfPermutationMap X σ)))
    intro p q
    constructor
    · rintro ⟨hp,b,hb,hq⟩
      exact ⟨⟨p,hp⟩,rfl,hb ▸ hq⟩
    · rintro ⟨a,ha,hq⟩
      exact ⟨ha ▸ a.property,⟨a.val,Set.mem_univ _⟩,ha,hq⟩

theorem gammaPermutationIso_apply (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (σ : Equiv.Perm (Fin n)) (a : A) :
    ((gammaPermutationIso A hA σ).equiv a).val = vfPermutation σ a.val := rfl

end IntegrationInACVF.Section5
