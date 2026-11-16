import «section 6».CarriedMapGraphFibres

/-! Carrying a full retained-label RV disc preserves proper covariance
and the homeomorphism property for arbitrary actual base maps. The full
graph-fibre identities supply both open domains and clopen ranges. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)

theorem carryLastMap_continuous (hCont : ContinuousOnGraphFibres f) :
    ContinuousOnGraphFibres (carryLastMap f k l hLabels) := by
  intro u v
  let D := graphFibreSource (carryLastMap f k l hLabels) u v
  have hMaps : Set.MapsTo Fin.init D (graphFibreSource f u v) := by
    intro a ha
    exact ((Set.ext_iff.mp (graphFibreSource_carryLastMap f k l hLabels u v) a).mp ha).1
  have hInit : ContinuousOn (fun a : Fin (n+1) → VF M => Fin.init a) D := by fun_prop
  have hHead := (hCont u v).comp hInit hMaps
  have hBoth : ContinuousOn (fun a : Fin (n+1) → VF M =>
      (Fin.snoc (graphFibreMap f u v (Fin.init a) : Fin n → VF M) (a (Fin.last n)) : Fin (n+1) → VF M)) D := by
    apply continuousOn_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (continuous_apply (Fin.last n)).continuousOn (s := D)
    · simpa only [Fin.snoc_castSucc,Function.comp_def] using (continuous_apply j).comp_continuousOn hHead
  apply hBoth.congr
  intro a ha
  have h := (graphFibre_carryLastMap_iff f k l hLabels u v a _).mp
    (graphFibreMap_graph (carryLastMap f k l hLabels) u v ha)
  have hOld := graphFibre_functional f u v h.1 (graphFibreMap_graph f u v (hMaps ha))
  calc
    graphFibreMap (carryLastMap f k l hLabels) u v a=
        Fin.snoc (Fin.init (graphFibreMap (carryLastMap f k l hLabels) u v a))
          (graphFibreMap (carryLastMap f k l hLabels) u v a (Fin.last n)) := (Fin.snoc_init_self _).symm
    _=Fin.snoc (graphFibreMap f u v (Fin.init a)) (a (Fin.last n)) := by rw [hOld,← h.2.1]

theorem carryLastMap_source_clopen
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hA : ProperInvariant S A.carrier) (hF : ProperCovariant f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    IsClopen (graphFibreSource (carryLastMap f k l hLabels) u v) := by
  obtain ⟨α,β,hα,hβ,hD,hR,hCov⟩ := hF.radii u v
  rw [graphFibreSource_carryLastMap_inter]
  exact ((hD.isClopen hv).preimage (by fun_prop)).inter
    ((rvCoordinateBundle_properInvariant h00 hc hκ hs hv A k hA).clopen_fibres hv u)

theorem carryLastMap_range_clopen
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hB : ProperInvariant S B.carrier) (hF : ProperCovariant f)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    IsClopen (graphFibreRange (carryLastMap f k l hLabels) u v) := by
  obtain ⟨α,β,hα,hβ,hD,hR,hCov⟩ := hF.radii u v
  rw [graphFibreRange_carryLastMap_inter]
  exact ((hR.isClopen hv).preimage (by fun_prop)).inter
    ((rvCoordinateBundle_properInvariant h00 hc hκ hs hv B l hB).clopen_fibres hv v)

theorem carryLastMap_properHomeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hF : ProperCovariantHomeomorphism f) : ProperCovariantHomeomorphism (carryLastMap f k l hLabels) := by
  have hA := hF.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  have hB := hF.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hF.bijective.surjective
  have hCont := carryLastMap_continuous f k l hLabels hF.continuous
  have hCov := properCovariant_of_clopen_ranges h00 hc hκ hs hv (carryLastMap f k l hLabels)
    (rvCoordinateBundle_properInvariant h00 hc hκ hs hv A k hA)
    (rvCoordinateBundle_properInvariant h00 hc hκ hs hv B l hB) hCont
    (fun u v => (carryLastMap_source_clopen f k l hLabels h00 hc hκ hs hv hA hF.covariant u v).isOpen)
    (carryLastMap_range_clopen f k l hLabels h00 hc hκ hs hv hB hF.covariant)
  exact properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ
    (carryLastMap f k l hLabels) hCov (carryLastMap_bijective f k l hLabels hF.bijective) hCont

end DiamondIntegral.Section6
