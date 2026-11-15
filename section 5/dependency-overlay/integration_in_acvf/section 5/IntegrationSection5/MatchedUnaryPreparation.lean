import IntegrationSection5.UnaryBijectionPreparation
import IntegrationSection5.UnaryRVCategory
import IntegrationSection5.UnarySpecialRelative
import Section5.GammaLift

/-! Constructed matched unary special preparations, with an actual RV[1]
isomorphism and its commuting square. The internal real base contains the
original base and imposes no additional smallness condition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m l : ℕ}

structure MatchedUnaryPreparation
    (A : Set (Point (M := M) 1 m)) (B : Set (Point (M := M) 1 l)) (e : A ≃ B) where
  codes : Set M
  real_contains : G.real ⊆ codes
  sourceA : DefSet (M := M) codes 1 m
  sourceB : DefSet (M := M) codes 1 l
  sourceA_eq : carrier sourceA = A
  sourceB_eq : carrier sourceB = B
  map : Map sourceA sourceB
  map_spec : ∀ a : sourceA, (map a).val =
    (e ⟨a.val,(Set.ext_iff.mp sourceA_eq a.val).mp a.property⟩).val
  bijective : Function.Bijective map
  arityA : ℕ
  arityB : ℕ
  targetA : DefSet (M := M) codes 1 arityA
  targetB : DefSet (M := M) codes 1 arityB
  specialA : SpecialBijection sourceA targetA
  specialB : SpecialBijection sourceB targetB
  gammaA : GammaChainDefinable G specialA.chain
  gammaB : GammaChainDefinable G specialB.chain
  pullbackA : IsRVPullback (carrier targetA)
  pullbackB : IsRVPullback (carrier targetB)
  conjugate_graph : GammaGraphDefinable G (pointMapGraph (unaryConjugate specialA specialB map))
  iso : pullbackObject targetA ≅ pullbackObject targetB
  square : ∀ a : targetA,
    unaryIsoHomMap iso (Map.toImage (rawKeyMap targetA) a) =
      Map.toImage (rawKeyMap targetB) (unaryConjugate specialA specialB map a)
  hom_graph : GammaGraphDefinable G (rvPullbackMapGraph (unaryIsoHomMap iso))
  inv_graph : GammaGraphDefinable G (rvPullbackMapGraph (unaryIsoInvMap iso))

theorem matched_unary_preparation_over {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (K : Set M) (A : Set (Point (M := M) 1 m)) (B : Set (Point (M := M) 1 l))
    (hA : GammaSetDefinable G A) (hB : GammaSetDefinable G B) (e : GammaIso G A B) :
    ∃ T : MatchedUnaryPreparation (G := G) A B e.equiv, K ⊆ T.codes := by
  obtain ⟨S0,hGS0,hAr0,hBr0,hfr0⟩ := common_gamma_presentation A B e.equiv hA hB e.graph
  let S := S0 ∪ K
  have hS0 : S0 ⊆ S := Set.subset_union_left
  have hGS : G.real ⊆ S := fun _ hx => hS0 (hGS0 hx)
  let hAr := SetDefinable.mono _ hAr0 hS0
  let hBr := SetDefinable.mono _ hBr0 hS0
  let hfr := RelationDefinable.mono _ _ hfr0 hS0
  let A0 : DefSet (M := M) S 1 m := PresentedSet.mk A hAr
  let B0 : DefSet (M := M) S 1 l := PresentedSet.mk B hBr
  let f0 : Map A0 B0 := Map.mk e.equiv hfr
  obtain ⟨R,hSR,r,s,A',B',TA,TB,hTA,hTB,hAP,hBP,hc,hback,hgraph,_⟩ :=
    lemma_5_2_gamma_presented hκ hs hsmall h00 δ hδ hδ1 F hGS f0 e.equiv.bijective hA hB e.graph
  let fR : Map (extendBase A0 hSR) (extendBase B0 hSR) :=
    @SpecialTransformations.DefinableGeometry.Map.extend LRV M (@CanonicalStructure.normalize M sM)
      (pointSpace 1 m) (pointSpace 1 l) S R A0 B0 f0 hSR
  obtain ⟨I,hI,hIG,hIinvG⟩ := lemma_5_3 hκ hs hsmall
    (unaryConjugate TA TB fR) (unaryConjugate_bijective TA TB fR e.equiv.bijective)
    hc hback hAP hBP hgraph
  refine ⟨{
    codes := R
    real_contains := fun x hx => hSR (hGS hx)
    sourceA := extendBase A0 hSR
    sourceB := extendBase B0 hSR
    sourceA_eq := rfl
    sourceB_eq := rfl
    map := fR
    map_spec := fun _ => rfl
    bijective := e.equiv.bijective
    arityA := r
    arityB := s
    targetA := A'
    targetB := B'
    specialA := TA
    specialB := TB
    gammaA := hTA
    gammaB := hTB
    pullbackA := hAP
    pullbackB := hBP
    conjugate_graph := hgraph
    iso := I
    square := hI
    hom_graph := hIG
    inv_graph := hIinvG },?_⟩
  exact fun _ hx => hSR (Or.inr hx)

theorem matched_unary_preparation {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) (F : VFFieldBase G.real)
    (A : Set (Point (M := M) 1 m)) (B : Set (Point (M := M) 1 l))
    (hA : GammaSetDefinable G A) (hB : GammaSetDefinable G B) (e : GammaIso G A B) :
    Nonempty (MatchedUnaryPreparation (G := G) A B e.equiv) := by
  obtain ⟨T,_⟩ := matched_unary_preparation_over hκ hs hsmall h00 δ hδ hδ1 F G.real A B hA hB e
  exact ⟨T⟩

end IntegrationInACVF.Section5
