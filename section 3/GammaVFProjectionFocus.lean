import «section 3».GammaRVProjectionFocus
import IntegrationSection5.GammaTraceProjection

/-! An ordinary Gamma focus pulls back across an injective selection of
VF coordinates and arbitrary retained RV coordinates. Its locus remains
an actual RV-pullback in all VF coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n N m l : ℕ}
variable {A : DefSet (M := M) S n m} {H : DefSet (M := M) S N l} {j : Fin n} {k : Fin m}

def gammaVFProjectionFocusGeometry (D : Focus A j k) (ι : Fin n → Fin N) (hι : Function.Injective ι)
    (ρ : Fin m → Fin l) (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A) :
    FocusGeometry (carrier H) (ι j) (ρ k) where
  tagged p hp := D.tagged (vfRVProjection ι ρ p) (hHA p hp)
  locus := {p | vfRVProjection ι ρ p ∈ D.locus} ∩ hull (carrier H)
  locus_pullback := isRVPullback_inter ((isRVPullback_iff _).mpr (by
    intro p hp q he
    exact (isRVPullback_iff _).mp D.locus_pullback _ hp _ (vfRVProjection_sameRV ι ρ he))) (hull_idem _)
  locus_subset := Set.inter_subset_right
  center p := D.center (vfRVProjection ι ρ p)
  independent p hp q hq he := by
    apply D.independent (vfRVProjection ι ρ p) ⟨hHA p hp.1,hp.2.1⟩
      (vfRVProjection ι ρ q) ⟨hHA q hq.1,hq.2.1⟩
    have h := congrArg (vfRVProjection ι ρ) he
    simpa only [erase,vfRVProjection_replace ι hι] using h
  center_mem := by
    intro p hp
    have hm := D.center_mem (vfRVProjection ι ρ p) ⟨hHA p hp.1,hp.2.1⟩
    have hr := D.toFocusGeometry.center_sameRV (vfRVProjection ι ρ p) ⟨hHA p hp.1,hp.2.1⟩
    refine ⟨?_,p,hp.1,sameRV_replace (ι j) p _ hr⟩
    exact Eq.mp (congrArg (fun q => q ∈ D.locus)
      (vfRVProjection_replace ι hι ρ j p (D.center (vfRVProjection ι ρ p))).symm) hm

def gammaVFProjectionFocusActive (D : Focus A j k) (ι : Fin n → Fin N) (hι : Function.Injective ι)
    (ρ : Fin m → Fin l) (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A) : DefSet (M := M) S N l :=
  PresentedSet.mk (carrier H ∩ (gammaVFProjectionFocusGeometry D ι hι ρ hHA).locus)
    (SetDefinable.inter _ (setDefinable H) (SetDefinable.inter _
      (vfRVProjection_preimage_definable ι ρ D.locus D.locus_definable) (hull_definable H)))

def gammaVFProjectionFocusActiveMap (D : Focus A j k) (ι : Fin n → Fin N) (hι : Function.Injective ι)
    (ρ : Fin m → Fin l) (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A) :
    Map (gammaVFProjectionFocusActive D ι hι ρ hHA) D.active :=
  Map.mk (fun p => ⟨vfRVProjection ι ρ p.val,hHA _ p.property.1,p.property.2.1⟩)
    (Map.graph_definable (vfRVProjectionMap ι ρ (gammaVFProjectionFocusActive D ι hι ρ hHA)))

def gammaVFProjectionFocus (D : Focus A j k) (ι : Fin n → Fin N) (hι : Function.Injective ι)
    (ρ : Fin m → Fin l) (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A) : Focus H (ι j) (ρ k) where
  toFocusGeometry := gammaVFProjectionFocusGeometry D ι hι ρ hHA
  locus_definable := SetDefinable.inter _
    (vfRVProjection_preimage_definable ι ρ D.locus D.locus_definable) (hull_definable H)
  center_graph := by
    have h := Map.graph_definable (Map.comp D.centerMap (gammaVFProjectionFocusActiveMap D ι hι ρ hHA))
    apply RelationDefinable.congr _ _ h
    intro p z
    constructor
    · rintro ⟨a,rfl,hz⟩
      exact ⟨a.property,(congrFun hz 0).symm⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      funext i
      fin_cases i
      exact hz.symm

theorem gammaVFProjectionFocus_eta (D : Focus A j k) (ι : Fin n → Fin N) (hι : Function.Injective ι)
    (ρ : Fin m → Fin l) (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A)
    (p : Point (M := M) N l) (hp : p ∈ carrier H) :
    vfRVProjection ι ρ ((gammaVFProjectionFocus D ι hι ρ hHA).toFocusGeometry.eta p) =
      D.toFocusGeometry.eta (vfRVProjection ι ρ p) := by
  have hh := subset_hull (carrier H) hp
  by_cases hd : vfRVProjection ι ρ p ∈ D.locus <;>
    simp [FocusGeometry.eta,gammaVFProjectionFocus,gammaVFProjectionFocusGeometry,hd,hh,
      vfRVProjection_replace ι hι] <;> rfl

theorem gammaVFProjectionFocus_gamma (D : Focus A j k) (ι : Fin n → Fin N) (hι : Function.Injective ι)
    (ρ : Fin m → Fin l) (hHA : ∀ p ∈ carrier H, vfRVProjection ι ρ p ∈ carrier A)
    (hH : GammaSetDefinable B (carrier H)) (hD : GammaFocusDefinable B D) :
    GammaFocusDefinable B (gammaVFProjectionFocus D ι hι ρ hHA) := by
  let L := gammaLogicInput B
  refine ⟨L.inter (gamma_vfRVProjection_preimage ι ρ hD.1) (L.hull hH),?_⟩
  let f := vfRVProjectionMap ι ρ (PresentedSet.univ (pointSpace (M := M) N l) B.real)
  have h := L.restrict_graph hH (L.comp_graph (L.real_map_graph f) hD.2)
  apply GammaGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨hp,q,⟨a,ha,hq⟩,hqA,hz⟩
    have he : q = vfRVProjection ι ρ p := hq.symm.trans (congrArg (vfRVProjection ι ρ) ha)
    rw [he] at hqA hz
    exact ⟨⟨hp,hqA.2,subset_hull _ hp⟩,hz⟩
  · rintro ⟨⟨hp,hd,hh⟩,hz⟩
    exact ⟨hp,vfRVProjection ι ρ p,⟨⟨p,Set.mem_univ _⟩,rfl,rfl⟩,⟨hHA p hp,hd⟩,hz⟩

end DiamondIntegral.Section3
