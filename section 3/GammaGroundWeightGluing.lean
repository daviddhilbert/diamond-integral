import «section 3».GammaGroundRVFinitePartitions
import «section 3».GammaGroundVolumeForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P : Space LRV M} {A : GammaGroundDefSet hc B P}

/-- Full-code volume forms glue over a finite disjoint injective atlas.
The graph is the actual finite union of chart graphs, so the original
ground is retained and no representative is adjoined. -/
theorem gammaGroundVolumeForm_glue_injective_charts {ι : Type} [Fintype ι]
    {Q : ι → Space LRV M} {D : ∀ i, GammaGroundDefSet hc B (Q i)}
    (a : ∀ i, GammaGroundMap (D i) A) (ha : ∀ i, Function.Injective (a i))
    (hd : ∀ i j, i ≠ j → Disjoint (a i).image.carrier (a j).image.carrier)
    (hcover : ∀ x : A, ∃ i, ∃ z : D i, a i z = x)
    (w : ∀ i, GammaGroundVolumeForm hc B (D i)) :
    ∃ W : GammaGroundVolumeForm hc B A, ∀ i z, (W (a i z)).val = (w i z).val := by
  have huniq (i j : ι) (x : D i) (y : D j) (he : a i x = a j y) : (w i x).val = (w j y).val := by
    by_cases hij : i = j
    · subst j
      exact congrArg (fun z : D i => (w i z).val) (ha i he)
    · have h1 : (a i x).val ∈ (a i).image.carrier := ⟨x,rfl⟩
      have h2 : (a i x).val ∈ (a j).image.carrier := ⟨y,(congrArg (fun z : A => z.val) he).symm⟩
      exact False.elim (Set.disjoint_left.mp (hd i j hij) h1 h2)
  have hchoice (x : A) : ∃ c : (Σ i : ι, D i), a c.1 c.2 = x := by
    obtain ⟨i,z,hz⟩ := hcover x
    exact ⟨⟨i,z⟩,hz⟩
  let choose := fun x : A => Classical.choose (hchoice x)
  have hchoose (x : A) : a (choose x).1 (choose x).2 = x := Classical.choose_spec (hchoice x)
  let f : A → GammaGroundDefSet.univ hc B (volumeGammaSpace hc) :=
    fun x => w (choose x).1 (choose x).2
  have hf (i : ι) (z : D i) : (f (a i z)).val = (w i z).val :=
    huniq (choose (a i z)).1 i (choose (a i z)).2 z (hchoose (a i z))
  let R := gammaGroundDefSetFiniteUnion Finset.univ (fun i => ((a i).pair (w i)).image)
  have hgraph : GammaGroundDefinable hc B (P.prod (volumeGammaSpace hc))
      {z | ∃ x : A, x.val = z.1 ∧ (f x).val = z.2} := by
    apply R.definable.congr
    intro z
    constructor
    · rintro ⟨i,_,x,hx⟩
      let p := a i x
      refine ⟨p,congrArg Prod.fst hx,?_⟩
      exact (hf i x).trans (congrArg Prod.snd hx)
    · rintro ⟨x,hx,hw⟩
      let c := choose x
      have hp : (a c.1 c.2).val = z.1 := (congrArg (fun y : A => y.val) (hchoose x)).trans hx
      have hw' : (w c.1 c.2).val = z.2 := hw
      exact ⟨c.1,Finset.mem_univ _,c.2,Prod.ext hp hw'⟩
  exact ⟨⟨f,hgraph⟩,hf⟩
end DiamondIntegral.Section3
