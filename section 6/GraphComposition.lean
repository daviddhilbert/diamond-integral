import «section 6».ProperHomeomorphisms

/-! Graph-fiber composition. The intermediate RV tag is fixed on an open
neighborhood before composing its two continuous VF maps. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m k r s t : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}
variable {C : DefSet (rawMixedSpace (M := M) k t) S}

theorem graphFibre_comp_iff (f : Map A B) (g : Map B C)
    (u : Fin r → RVInfinity M) (w : Fin t → RVInfinity M)
    (a : Fin n → VF M) (c : Fin k → VF M) :
    graphFibre (g.comp f) u w a c ↔ ∃ v : Fin s → RVInfinity M, ∃ b : Fin m → VF M,
      graphFibre f u v a b ∧ graphFibre g v w b c := by
  constructor
  · rintro ⟨p,hp,hgp⟩
    exact ⟨(f p).val.2,(f p).val.1,⟨p,hp,rfl⟩,f p,rfl,hgp⟩
  · rintro ⟨v,b,⟨p,hp,hfp⟩,⟨q,hq,hgq⟩⟩
    have he : f p = q := Subtype.ext (hfp.trans hq.symm)
    exact ⟨p,hp,by change (g (f p)).val = _; rw [he]; exact hgq⟩

theorem graphFibreSource_comp_iff (f : Map A B) (g : Map B C)
    (u : Fin r → RVInfinity M) (w : Fin t → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource (g.comp f) u w ↔ ∃ v : Fin s → RVInfinity M,
      a ∈ graphFibreSource f u v ∧ graphFibreMap f u v a ∈ graphFibreSource g v w := by
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨v,b,hf,hg⟩ := (graphFibre_comp_iff f g u w a c).mp hc
    have ha : a ∈ graphFibreSource f u v := ⟨b,hf⟩
    have he : graphFibreMap f u v a = b := graphFibre_functional f u v (graphFibreMap_graph f u v ha) hf
    exact ⟨v,ha,he.symm ▸ ⟨c,hg⟩⟩
  · rintro ⟨v,ha,b,hb⟩
    exact ⟨b,(graphFibre_comp_iff f g u w a b).mpr
      ⟨v,graphFibreMap f u v a,graphFibreMap_graph f u v ha,hb⟩⟩

theorem graphFibreMap_comp_eq (f : Map A B) (g : Map B C)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (w : Fin t → RVInfinity M)
    {a : Fin n → VF M} (ha : a ∈ graphFibreSource f u v)
    (hfa : graphFibreMap f u v a ∈ graphFibreSource g v w) :
    graphFibreMap (g.comp f) u w a = graphFibreMap g v w (graphFibreMap f u v a) := by
  have hG := (graphFibre_comp_iff f g u w a _).mpr
    ⟨v,graphFibreMap f u v a,graphFibreMap_graph f u v ha,graphFibreMap_graph g v w hfa⟩
  exact graphFibre_functional (g.comp f) u w (graphFibreMap_graph (g.comp f) u w ⟨_,hG⟩) hG

theorem inverse_comp_eq (f : Map A B) (g : Map B C)
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    (g.comp f).inverse (hg.comp hf) = (f.inverse hf).comp (g.inverse hg) := by
  apply Map.ext
  intro c
  apply (hg.comp hf).injective
  have hright : (g.comp f) (((f.inverse hf).comp (g.inverse hg)) c) = c := by
    change g (f (f.inverse hf (g.inverse hg c))) = c
    rw [Map.apply_inverse,Map.apply_inverse]
  exact (Map.apply_inverse (g.comp f) (hg.comp hf) c).trans hright.symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def GraphContinuous (f : Map A B) : Prop :=
  (∀ u v, IsOpen (graphFibreSource f u v)) ∧ ContinuousOnGraphFibres f

theorem graphContinuous_of_properCovariant
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {f : Map A B} (hcov : ProperCovariant f) (hcont : ContinuousOnGraphFibres f) :
    GraphContinuous f := by
  refine ⟨fun u v => ?_,hcont⟩
  obtain ⟨_,_,_,_,hD,_,_⟩ := hcov.radii u v
  exact hD.isOpen hv

theorem GraphContinuous.comp {f : Map A B} {g : Map B C}
    (hg : GraphContinuous g) (hf : GraphContinuous f) : GraphContinuous (g.comp f) := by
  have hNopen (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (w : Fin t → RVInfinity M) :
      IsOpen (graphFibreSource f u v ∩ graphFibreMap f u v ⁻¹' graphFibreSource g v w) :=
    (hf.2 u v).isOpen_inter_preimage (hf.1 u v) (hg.1 v w)
  constructor
  · intro u w
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    obtain ⟨v,haF,haG⟩ := (graphFibreSource_comp_iff f g u w a).mp ha
    exact Filter.mem_of_superset ((hNopen u v w).mem_nhds ⟨haF,haG⟩)
      (fun b hb => (graphFibreSource_comp_iff f g u w b).mpr ⟨v,hb.1,hb.2⟩)
  · intro u w a ha
    obtain ⟨v,haF,haG⟩ := (graphFibreSource_comp_iff f g u w a).mp ha
    have hF : ContinuousAt (graphFibreMap f u v) a := (hf.2 u v).continuousAt ((hf.1 u v).mem_nhds haF)
    have hG : ContinuousAt (graphFibreMap g v w) (graphFibreMap f u v a) :=
      (hg.2 v w).continuousAt ((hg.1 v w).mem_nhds haG)
    have he : graphFibreMap (g.comp f) u w =ᶠ[𝓝 a] graphFibreMap g v w ∘ graphFibreMap f u v :=
      Filter.mem_of_superset ((hNopen u v w).mem_nhds ⟨haF,haG⟩)
        (fun b hb => graphFibreMap_comp_eq f g u v w hb.1 hb.2)
    exact ((hG.comp hF).congr_of_eventuallyEq he).continuousWithinAt

end DiamondIntegral.Section6
