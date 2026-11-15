import IntegrationSection5.GammaTraceProjection
import IntegrationSection5.TraceFlags

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m a b : ℕ}
theorem gamma_membershipMap_graph_mixed (A D : DefSet (M := M) S n m)
    (hA : GammaSetDefinable G (carrier A)) (hD : GammaSetDefinable G (carrier D)) :
    GammaGraphDefinable G (pointMapGraph (membershipMap A D)) := by
  let L := gammaLogicInput G
  let U := PresentedSet.univ (pointSpace (M := M) n m) G.real
  let E : DefSet (M := M) G.real n m :=
    @SpecialTransformations.DefinableGeometry.DefSet.empty LRV M
      (CanonicalStructure.normalize (M := M)) (pointSpace n m) G.real
  have hyes := L.restrict_graph (L.inter hA hD) (L.real_map_graph (membershipMap U U))
  have hno := L.restrict_graph (L.sdiff hA hD) (L.real_map_graph (membershipMap U E))
  apply GammaGraphDefinable.congr (L.union_graph hyes hno)
  intro p q
  constructor
  · rintro (⟨⟨hp,hD⟩,a,ha,hq⟩ | ⟨⟨hp,hD⟩,a,ha,hq⟩)
    · refine ⟨⟨p,hp⟩,rfl,?_⟩
      change membershipPoint D p = q
      have he : membershipPoint D p = membershipPoint U a.val := by
        simp [membershipPoint,hD,U,carrier,SpecialTransformations.DefinableGeometry.DefSet.univ]
      exact he.trans hq
    · refine ⟨⟨p,hp⟩,rfl,?_⟩
      change membershipPoint D p = q
      have he : membershipPoint D p = membershipPoint E a.val := by
        simp [membershipPoint,hD,E,carrier,SpecialTransformations.DefinableGeometry.DefSet.empty]
      exact he.trans hq
  · rintro ⟨a,rfl,hq⟩
    by_cases ha : a.val ∈ carrier D
    · left
      refine ⟨⟨a.property,ha⟩,⟨a.val,Set.mem_univ _⟩,rfl,?_⟩
      change membershipPoint U a.val = q
      have he : membershipPoint U a.val = membershipPoint D a.val := by
        simp [membershipPoint,ha,U,carrier,SpecialTransformations.DefinableGeometry.DefSet.univ]
      exact he.trans hq
    · right
      refine ⟨⟨a.property,ha⟩,⟨a.val,Set.mem_univ _⟩,rfl,?_⟩
      change membershipPoint E a.val = q
      have he : membershipPoint E a.val = membershipPoint D a.val := by
        simp [membershipPoint,ha,E,carrier,SpecialTransformations.DefinableGeometry.DefSet.empty]
      exact he.trans hq

def gammaRVMapOfPointMap {A : DefSet (M := M) S n m} {D : DefSet (M := M) S 0 a}
    (f : Map A D) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    IntegrationInACVF.Section4.GammaRVMap G (carrier A) a where
  toFun x := (f x).val.2
  graph := by
    apply GammaGraphDefinable.congr hf
    intro p q
    constructor
    · rintro ⟨x,hx,hq⟩
      exact ⟨x,hx,congrArg Prod.snd hq⟩
    · rintro ⟨x,hx,hq⟩
      exact ⟨x,hx,Prod.ext (Subsingleton.elim _ _) hq⟩

theorem gamma_pairRVMaps {A : DefSet (M := M) S n m}
    {D : DefSet (M := M) S 0 a} {E : DefSet (M := M) S 0 b}
    (f : Map A D) (g : Map A E) (hf : GammaGraphDefinable G (pointMapGraph f))
    (hg : GammaGraphDefinable G (pointMapGraph g)) :
    GammaGraphDefinable G (pointMapGraph (pairRVMaps f g)) := by
  have h := (IntegrationInACVF.Section4.GammaRVMap.pair (gammaRVMapOfPointMap f hf) (gammaRVMapOfPointMap g hg)).graph
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨x,hx,hq⟩
    exact ⟨x,hx,Prod.ext (Subsingleton.elim _ _) hq⟩
  · rintro ⟨x,hx,hq⟩
    exact ⟨x,hx,congrArg Prod.snd hq⟩

theorem gamma_constantRVMap {A : DefSet (M := M) S n m} (hA : GammaSetDefinable G (carrier A)) (d : ℕ) :
    GammaGraphDefinable G (pointMapGraph (constantRVMap A d)) := by
  have h := (IntegrationInACVF.Section4.GammaRVMap.zero G (carrier A) hA d).graph
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨x,hx,hq⟩
    exact ⟨x,hx,Prod.ext (Subsingleton.elim _ _) hq⟩
  · rintro ⟨x,hx,hq⟩
    exact ⟨x,hx,congrArg Prod.snd hq⟩

theorem GammaUniformTrace.flagMap {l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (T : UniformRelativeTrace S n A B) (hT : GammaUniformTrace (G := G) T) :
    GammaGraphDefinable G (pointMapGraph T.flagMap) := by
  induction T with
  | nil A => exact gamma_constantRVMap hT 0
  | canonical i tail ih =>
    exact gamma_composition_graph (coordinateCanonicalBijection _ i) tail.flagMap
      (gamma_coordinateCanonical_graph _ hT.1 i) (ih hT.2)
  | focus D tail ih =>
    exact gamma_pairRVMaps (membershipMap _ (PresentedSet.mk D.locus D.locus_definable))
      (Map.comp tail.flagMap D.toImage)
      (gamma_membershipMap_graph_mixed _ _ hT.1 hT.2.1.locus)
      (gamma_composition_graph D.toImage tail.flagMap (gamma_fibre_eta_graph D hT.1 hT.2.1) (ih hT.2.2))

end IntegrationInACVF.Section5
