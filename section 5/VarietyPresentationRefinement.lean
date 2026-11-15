import «section 5».FiniteAffineVarietyPresentations
import «section 5».VarietyMorphisms

/-! Actual finite immersed partitions compose, and pull back along
regular morphisms after reduction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory
variable {X Y : Object}

def ImmersedPresentation.refine (c : ImmersedPresentation X Set.univ)
    (d : ∀ i, ImmersedPresentation (c.piece i) Set.univ) : ImmersedPresentation X Set.univ := by
  letI := c.finite
  letI (i : c.index) := (d i).finite
  letI (i : c.index) := c.immersion i
  letI (i : c.index) (j : (d i).index) := (d i).immersion j
  exact {
    index := Σ i,(d i).index
    finite := inferInstance
    piece := fun a => (d a.1).piece a.2
    inclusion := fun a => (c.inclusion a.1).comp ((d a.1).inclusion a.2)
    immersion := fun a => inferInstance
    contained := fun _ => Set.subset_univ _
    partition := fun x => by
      simp only [Set.mem_univ,true_iff]
      obtain ⟨i,⟨y,hy⟩,hi⟩ := (c.partition x).mp (Set.mem_univ _)
      obtain ⟨j,⟨z,hz⟩,hj⟩ := ((d i).partition y).mp (Set.mem_univ _)
      refine ⟨⟨i,j⟩,⟨z,?_⟩,?_⟩
      · change (c.inclusion i).hom ((d i).inclusion j |>.hom <| z) = x
        rw [hz,hy]
      · rintro ⟨k,l⟩ ⟨w,hw⟩
        have hki : k = i := hi k ⟨((d k).inclusion l).hom w,hw⟩
        cases hki
        have hly : ((d i).inclusion l).hom w = y :=
          (c.inclusion i).hom.isEmbedding.injective (hw.trans hy.symm)
        have hlj : l = j := hj l ⟨w,hly⟩
        exact congrArg (fun j => (⟨i,j⟩ : Σ i,(d i).index)) hlj }

def ImmersedPresentation.pullback (d : ImmersedPresentation Y Set.univ)
    (f : Morphism X Y) : ImmersedPresentation X Set.univ := by
  letI (j : d.index) := d.immersion j
  exact {
    index := d.index
    finite := d.finite
    piece := fun j => commonImmersionObject f (d.inclusion j)
    inclusion := fun j => commonImmersionLeft f (d.inclusion j)
    immersion := fun _ => reducedPullbackFst_immersion _ _
    contained := fun _ => Set.subset_univ _
    partition := fun x => by
      simp only [Set.mem_univ,true_iff]
      have he (j : d.index) : x ∈ Set.range (commonImmersionLeft f (d.inclusion j)).hom ↔
          f.hom x ∈ Set.range (d.inclusion j).hom := by
        change x ∈ Set.range (reducedPullbackFst f.hom (d.inclusion j).hom) ↔ _
        rw [reducedPullbackFst_range]
        rfl
      obtain ⟨j,hj,hu⟩ := (d.partition (f.hom x)).mp (Set.mem_univ _)
      exact ⟨j,(he j).mpr hj,fun k hk => hu k ((he k).mp hk)⟩ }

end DiamondIntegral.Section5.EquivariantVariety
