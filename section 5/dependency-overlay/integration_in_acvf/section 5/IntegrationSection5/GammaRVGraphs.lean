import IntegrationSection5.GammaGraphOperations
import Section5.GammaLift

/-! Full original-base graphs for maps between the actual raw RV domains,
including inverses and maps that keep every underlying RV coordinate. -/
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
variable {G : GammaParameters.Base (M := M)} {S : Set M} {a b c : ℕ}

def rvMapGraph {A : PresentedSet (rawRVSpace (M := M) a) S}
    {B : PresentedSet (rawRVSpace (M := M) b) S} (f : Map A B)
    (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) : Prop :=
  ∃ u : A, u.val = p.2 ∧ (f u).val = q.2

theorem gamma_rvMap_comp
    {A : PresentedSet (rawRVSpace (M := M) a) S} {B : PresentedSet (rawRVSpace (M := M) b) S}
    {C : PresentedSet (rawRVSpace (M := M) c) S} (f : Map A B) (g : Map B C)
    (hf : GammaGraphDefinable G (rvMapGraph f)) (hg : GammaGraphDefinable G (rvMapGraph g)) :
    GammaGraphDefinable G (rvMapGraph (Map.comp g f)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).comp_graph hf hg)
  intro p q
  constructor
  · rintro ⟨z,⟨u,hu,huz⟩,⟨v,hv,hvq⟩⟩
    have he : v = f u := Subtype.ext (hv.trans huz.symm)
    exact ⟨u,hu,(congrArg (fun v : B => (g v).val) he).symm.trans hvq⟩
  · rintro ⟨u,hu,hq⟩
    exact ⟨(Fin.elim0,(f u).val),⟨u,hu,rfl⟩,f u,rfl,hq⟩

theorem gamma_rvMap_inverse
    {A : PresentedSet (rawRVSpace (M := M) a) S} {B : PresentedSet (rawRVSpace (M := M) b) S}
    (f : Map A B) (hf : Function.Bijective f) (hG : GammaGraphDefinable G (rvMapGraph f)) :
    GammaGraphDefinable G (rvMapGraph (Map.inverse f hf)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).swap_graph hG)
  intro p q
  constructor
  · rintro ⟨u,hu,hp⟩
    exact ⟨f u,hp,congrArg Subtype.val (Map.inverse_apply f hf u) |>.trans hu⟩
  · rintro ⟨v,hv,hq⟩
    exact ⟨Map.inverse f hf v,hq,(congrArg Subtype.val (Map.apply_inverse f hf v)).trans hv⟩

theorem gamma_rvMap_identity_values
    {A B : PresentedSet (rawRVSpace (M := M) a) S} (f : Map A B)
    (hf : ∀ u : A, (f u).val = u.val)
    (hA : GammaSetDefinable G {p : Point (M := M) 0 a | p.2 ∈ carrier A}) :
    GammaGraphDefinable G (rvMapGraph f) := by
  let X := PresentedSet.univ (pointSpace (M := M) 0 a) G.real
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hA
    ((gammaLogicInput G).real_map_graph (Map.id X)))
  intro p q
  constructor
  · rintro ⟨hp,u,hu,huq⟩
    have hpq : p = q := hu.symm.trans huq
    exact ⟨⟨p.2,hp⟩,rfl,(hf _).trans (congrArg Prod.snd hpq)⟩
  · rintro ⟨u,hu,huq⟩
    have hpq : p = q := Prod.ext (Subsingleton.elim _ _) (hu.symm.trans ((hf u).symm.trans huq))
    have hp : p.2 ∈ carrier A := hu ▸ u.property
    exact ⟨hp,⟨p,Set.mem_univ _⟩,rfl,hpq⟩

end IntegrationInACVF.Section5
