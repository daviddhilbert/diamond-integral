import IntegrationSection5.GammaMapPresentation
import IntegrationSection5.PulledFocusDefinability

/-! A genuine common real presentation of an actual Gamma-definable scalar
function. Its RV representatives remain internal to the presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m : ℕ}

theorem scalar_real_presentation (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (c : Point (M := M) n m → VF (M := M))
    (hc : GammaScalarGraphDefinable G (fun p x => p ∈ A ∧ x = c p)) :
    ∃ S : Set M, G.real ⊆ S ∧
      SetDefinable (pointSpace n m) S A ∧
      RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) S
        (fun p z => p ∈ A ∧ z 0 = c p) := by
  let C := (Set.univ : Set (Point (M := M) 1 0))
  let g (a : A) : C := ⟨(![c a.val],Fin.elim0),Set.mem_univ _⟩
  have hC : GammaSetDefinable G C := (gammaLogicInput G).real_set _
    (setDefinable (PresentedSet.univ (pointSpace (M := M) 1 0) G.real))
  have hg : GammaGraphDefinable G (fun p q => ∃ a : A, a.val = p ∧ (g a).val = q) := by
    apply GammaGraphDefinable.congr hc
    intro p q
    constructor
    · rintro ⟨hp,hq⟩
      refine ⟨⟨p,hp⟩,rfl,Prod.ext ?_ (Subsingleton.elim _ _)⟩
      funext j
      fin_cases j
      exact hq.symm
    · rintro ⟨a,ha,hq⟩
      refine ⟨ha ▸ a.property,?_⟩
      exact (congrArg (fun z : Point (M := M) 1 0 => vfAt z 0) hq).symm.trans (congrArg c ha)
  obtain ⟨S,hGS,hAr,hCr,hgr⟩ := common_gamma_presentation A C g hA hC hg
  let AR : DefSet (M := M) S n m := @PresentedSet.mk M sM (pointSpace n m) S A hAr
  let CR : DefSet (M := M) S 1 0 := @PresentedSet.mk M sM (pointSpace 1 0) S C hCr
  let gr : Map AR CR := @Map.mk M sM (pointSpace n m) (pointSpace 1 0) S AR CR g hgr
  let f := Map.comp (unaryVFProjection CR) gr
  refine ⟨S,hGS,hAr,?_⟩
  apply RelationDefinable.congr _ _ (Map.graph_definable f)
  intro p z
  constructor
  · rintro ⟨a,ha,hz⟩
    refine ⟨ha ▸ a.property,?_⟩
    exact (congrFun hz 0).symm.trans (congrArg c ha)
  · rintro ⟨hp,hz⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    funext j
    fin_cases j
    exact hz.symm

end IntegrationInACVF.Section5
