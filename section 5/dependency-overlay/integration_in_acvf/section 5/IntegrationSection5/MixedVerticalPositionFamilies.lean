import IntegrationSection4.VerticalCharts
import IntegrationSection4.GammaScalarFamilies

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace IntegrationInACVF.Section5.MixedVerticalPositionFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ} {B : DefSet (M := M) S 2 l}

def domain (B : DefSet (M := M) S 2 l) (C : Set (Point (M := M) 2 l)) :
    Set (Point (M := M) 1 l) :=
  {u | ∃ b : B, b.val ∈ C ∧ dropHead id b.val = u}

def includedKey (C : Set (Point (M := M) 2 l)) (u : domain B C) : VerticalOffsets.keyImage B :=
  ⟨u.val,by
    obtain ⟨b,_,he⟩ := u.property
    exact ⟨b,he⟩⟩

def position (T : RelativeBijection (PresentedSet.univ (pointSpace 2 m) S) B)
    (C : Set (Point (M := M) 2 l)) (u : domain B C) : VF (M := M) :=
  VerticalOffsets.offsetValue T (includedKey C u)

theorem domain_definable (G : GammaParameters.Base (M := M))
    (B : DefSet (M := M) G.real 2 l) (C : Set (Point (M := M) 2 l))
    (hC : GammaSetDefinable G C) : GammaSetDefinable G (domain B C) :=
  (gammaLogicInput G).image_real (VerticalOffsets.keyMap B) hC

theorem position_definable (G : GammaParameters.Base (M := M))
    {B : DefSet (M := M) G.real 2 l}
    (T : RelativeBijection (PresentedSet.univ (pointSpace 2 m) G.real) B)
    (C : Set (Point (M := M) 2 l)) (hC : GammaSetDefinable G C) :
    GammaScalarGraphDefinable G (fun p y => ∃ u : domain B C, u.val = p ∧ position T C u = y) := by
  let hΓ := gammaLogicInput G
  have h := hΓ.restrict_graph (domain_definable G B C hC)
    (hΓ.real_scalar_graph (VerticalOffsets.offsetMap T))
  apply GammaGraphDefinable.congr h
  intro p q
  change (p ∈ domain B C ∧ ∃ a : VerticalOffsets.keyImage B,
    a.val = p ∧ VerticalOffsets.offsetValue T a = vfAt q 0) ↔ _
  constructor
  · rintro ⟨hp,a,ha,hy⟩
    let u : domain B C := ⟨p,hp⟩
    have he : includedKey C u = a := Subtype.ext ha.symm
    exact ⟨u,rfl,by change VerticalOffsets.offsetValue T (includedKey C u) = _; rwa [he]⟩
  · rintro ⟨u,hu,hy⟩
    exact ⟨hu ▸ u.property,includedKey C u,hu,hy⟩

/-- The positioning function in a vertical chart has a full original-base
raw family graph, with invalid RV contexts empty. -/
theorem family_graph (G : GammaParameters.Base (M := M))
    {B : DefSet (M := M) G.real 2 l}
    (T : RelativeBijection (PresentedSet.univ (pointSpace 2 m) G.real) B)
    (C : Set (Point (M := M) 2 l)) (hC : GammaSetDefinable G C) :
    FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G)
      (GammaScalarFamilies.family (domain B C)) (GammaScalarFamilies.value (position T C)) :=
  GammaScalarFamilies.graph_definable G _ _ (position_definable G T C hC)

theorem head_body (T : RelativeBijection (PresentedSet.univ (pointSpace 2 m) S) B)
    (j : Fin l) (hTag : Tagged (carrier B) 0 j) (b : B) :
    VerticalOffsets.headBody T b =
      {y | ∃ a : PresentedSet.univ (pointSpace (M := M) 2 m) S,
        vfAt a.val 0 = y ∧ vfAt a.val 1 = vfAt b.val 1 ∧ (T.toMap a).val.2 = b.val.2} := by
  ext y
  constructor
  · rintro ⟨p,⟨a,hap,he,ht⟩,hpy⟩
    refine ⟨a,(congrArg (fun p : Point (M := M) 2 m => vfAt p 0) hap).trans hpy,?_,
      ((sameRV_iff _ _).mp he).2⟩
    exact (T.tail a 0).symm.trans (ht 0)
  · rintro ⟨a,hay,hat,hal⟩
    have ht : TailEq (T.toMap a).val b.val := by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (T.tail a 0).trans hat
    have he : SameRV (T.toMap a).val b.val := by
      apply (sameRV_iff _ _).mpr
      refine ⟨?_,hal⟩
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact (hTag _ (T.toMap a).property).symm.trans
          ((congrFun hal j).trans (hTag _ b.property))
      · exact congrArg rv (ht k)
    exact ⟨a.val,⟨a,rfl,he,ht⟩,hay⟩

end IntegrationInACVF.Section5.MixedVerticalPositionFamilies
