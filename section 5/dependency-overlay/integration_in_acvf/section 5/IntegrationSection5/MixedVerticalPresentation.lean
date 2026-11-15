import IntegrationSection5.MixedVerticalPositionFamilies
import IntegrationSection4.BalancedFibres

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace IntegrationInACVF.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- An actual uniform vertical presentation. Coordinate 0 is the vertical
coordinate and coordinate 1 is the first coordinate of the paper's VF².
All fields describe functions and point-set equalities, not existence axioms. -/
structure MixedVerticalPresentation (G : GammaParameters.Base (M := M))
    {m : ℕ} (A : Set (Point (M := M) 2 m)) where
  arity : ℕ
  domain : Set (Point (M := M) 1 arity)
  domain_definable : GammaSetDefinable G domain
  paradigm_index : Fin arity
  position : domain → VF (M := M)
  position_graph : GammaScalarGraphDefinable G (fun p y => ∃ u : domain, u.val = p ∧ position u = y)
  projection : A → domain
  projection_graph : GammaGraphDefinable G (fun p q => ∃ a : A, a.val = p ∧ (projection a).val = q)
  first : ∀ a : A, vfAt (projection a).val 0 = vfAt a.val 1
  fibres : ∀ u : domain, {y | ∃ a : A, projection a = u ∧ vfAt a.val 0 = y} =
    BalancedFibres.translatedRV (u.val.2 paradigm_index) (position u)
  inverse_rv : ∀ a b : A, SameRV (projection a).val (projection b).val → SameRV a.val b.val

namespace MixedVerticalPresentation

theorem exists_presentation {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) {m : ℕ} (A : Set (Point (M := M) 2 m))
    (hA : GammaSetDefinable G A) : Nonempty (MixedVerticalPresentation G A) := by
  obtain ⟨l,B,T,hB,⟨j,hTag⟩,hC,hCHead,hSlices⟩ :=
    VerticalCharts.exists_chart hs h00 G hsmall hGenerated A hA
  let U := PresentedSet.univ (pointSpace (M := M) 2 m) G.real
  let C := {q | ∃ a : U, a.val ∈ A ∧ (T.toMap a).val = q}
  let D := MixedVerticalPositionFamilies.domain B C
  let g := MixedVerticalPositionFamilies.position T C
  let H (a : A) : D :=
    ⟨dropHead id (T.toMap ⟨a.val,Set.mem_univ _⟩).val,
      T.toMap ⟨a.val,Set.mem_univ _⟩,⟨⟨a.val,Set.mem_univ _⟩,a.property,rfl⟩,rfl⟩
  have hH : GammaGraphDefinable G (fun (p : Point (M := M) 2 m) (q : Point (M := M) 1 l) =>
      ∃ a : A, a.val = p ∧ (H a).val = q) := by
    let K := Map.comp (VerticalOffsets.keyMap B) T.toMap
    have hh := (gammaLogicInput G).restrict_graph hA ((gammaLogicInput G).real_map_graph K)
    apply GammaGraphDefinable.congr hh
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hq⟩
      refine ⟨⟨a.val,ha.symm ▸ hp⟩,ha,hq⟩
    · rintro ⟨a,ha,hq⟩
      exact ⟨ha ▸ a.property,⟨a.val,Set.mem_univ _⟩,ha,hq⟩
  refine ⟨⟨l,D,MixedVerticalPositionFamilies.domain_definable G B C hC,j,g,
    MixedVerticalPositionFamilies.position_definable G T C hC,H,hH,?_,?_,?_⟩⟩
  · intro a
    exact T.tail ⟨a.val,Set.mem_univ _⟩ 0
  · intro u
    obtain ⟨b,hbC,hbu⟩ := u.property
    have hKey : MixedVerticalPositionFamilies.includedKey C u = VerticalOffsets.toKey B b := Subtype.ext hbu.symm
    have hPos : g u = VerticalOffsets.offsetValue T (VerticalOffsets.toKey B b) :=
      congrArg (VerticalOffsets.offsetValue T) hKey
    have hPar : u.val.2 j = rv (vfAt b.val 0) :=
      (congrFun (congrArg Prod.snd hbu) j).symm.trans (hTag _ b.property)
    have hBody : VerticalOffsets.headBody T b = BalancedFibres.translatedRV (u.val.2 j) (g u) := by
      rw [hPar,hPos,BalancedFibres.translatedRV_eq_image]
      exact (hSlices b hbC).2
    rw [← hBody]
    ext y
    constructor
    · rintro ⟨a,ha,hay⟩
      let aU : U := ⟨a.val,Set.mem_univ _⟩
      have hd : dropHead id (T.toMap aU).val = dropHead id b.val :=
        (congrArg Subtype.val ha).trans hbu.symm
      have hTail : vfAt a.val 1 = vfAt b.val 1 :=
        (T.tail aU 0).symm.trans (congrArg (fun p : Point (M := M) 1 l => vfAt p 0) hd)
      apply (Set.ext_iff.mp (MixedVerticalPositionFamilies.head_body T j hTag b) y).mpr
      exact ⟨aU,hay,hTail,congrArg (fun q : Point (M := M) 1 l => q.2) hd⟩
    · rintro ⟨p,hp,hy⟩
      have hpA := (hSlices b hbC).1 hp
      obtain ⟨a,ha,he,ht⟩ := hp
      let aA : A := ⟨a.val,ha.symm ▸ hpA⟩
      have hd : dropHead id (T.toMap a).val = dropHead id b.val := by
        apply Prod.ext
        · funext i; exact ht i
        · exact ((sameRV_iff _ _).mp he).2
      refine ⟨aA,Subtype.ext (hd.trans hbu),?_⟩
      exact (congrArg (fun p : Point (M := M) 2 m => vfAt p 0) ha).trans hy
  · intro a b he
    let aU : U := ⟨a.val,Set.mem_univ _⟩
    let bU : U := ⟨b.val,Set.mem_univ _⟩
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
    have hLabels : (T.toMap aU).val.2 = (T.toMap bU).val.2 := hl
    have hFull : SameRV (T.toMap aU).val (T.toMap bU).val := by
      apply (sameRV_iff _ _).mpr
      refine ⟨?_,hLabels⟩
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact (hTag _ (T.toMap aU).property).symm.trans
          ((congrFun hLabels j).trans (hTag _ (T.toMap bU).property))
      · have hk : k = 0 := Subsingleton.elim _ _
        subst k
        exact hv 0
    exact T.inverse_rv aU bU hFull

end MixedVerticalPresentation
end IntegrationInACVF.Section5
