import «section 6».MeasuredRVLiftGeometry

/-! Fixed source and target old labels cut out either an empty graph
fibre or an entire target RV polydisc for a bijective lift. Total charts
also directly prove that every graph-fibre source is open. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem graphFibreSource_isOpen_of_mixedDerivatives
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map A B)
    (hD : ∀ p : A, ∃ L, HasMixedVFDerivativeAt f p L) (u v) :
    IsOpen (graphFibreSource f u v) := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph f u v ha
  have hpa := congrArg (fun z : Mixed M n r => z.1) hp
  have hpu := congrArg (fun z : Mixed M n r => z.2) hp
  have hfv := congrArg (fun z : Mixed M n s => z.2) hfp
  obtain ⟨L,F,⟨ρ,hρ⟩,_⟩ := hD p
  apply Filter.mem_of_superset (vfBall_mem_nhds hv a ρ)
  intro x hx
  have hx' : x ∈ vfBall p.val.1 ρ := by rw [hpa]; exact hx
  obtain ⟨hxA,hfx⟩ := hρ x hx'
  exact ⟨F x,⟨⟨(x,p.val.2),hxA⟩,Prod.ext rfl hpu,hfx.trans (Prod.ext rfl hfv)⟩⟩

theorem rvIsoLift_graphFibreRange_eq_fibre_of_nonempty
    {U V : RVObject (M := M) S n} (e : U ≅ V)
    (f : Map (rvLift U) (rvLift V)) (hf : Function.Surjective f)
    (hlabel : ∀ p, e.hom.map.graph p.val.2 (f p).val.2)
    (u : Fin U.arity → RVInfinity M) (v : Fin V.arity → RVInfinity M)
    (hne : (graphFibreRange f u v).Nonempty) :
    graphFibreRange f u v = vfFibre (rvLift V).carrier v := by
  obtain ⟨b,a,p,hp,hfp⟩ := hne
  have hpu := congrArg (fun z : Mixed M n U.arity => z.2) hp
  have hpv := congrArg (fun z : Mixed M n V.arity => z.2) hfp
  apply Set.Subset.antisymm
  · exact fun _ hb => graphFibreRange_subset f u v hb
  · intro y hy
    obtain ⟨q,hq⟩ := hf ⟨(y,v),hy⟩
    have he : e.hom.map (liftLabelMap U q) = e.hom.map (liftLabelMap U p) := by
      rw [← liftLabelMap_target_of_graph e.hom.map f hlabel q,
        ← liftLabelMap_target_of_graph e.hom.map f hlabel p]
      apply Subtype.ext
      change (f q).val.2 = (f p).val.2
      rw [hq]
      exact hpv.symm
    have he' := congrArg e.inv.map he
    rw [rvIso_inv_apply,rvIso_inv_apply] at he'
    have hqu : q.val.2 = u := (congrArg Subtype.val he').trans hpu
    exact ⟨q.val.1,q,Prod.ext rfl hqu,congrArg Subtype.val hq⟩

theorem measuredRVIsoLift_graphFibreRange_isClopen
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map (rvLift U.object) (rvLift V.object)) (hf : Function.Surjective f)
    (hlabel : ∀ p, e.iso.hom.map.graph p.val.2 (f p).val.2) (u v) :
    IsClopen (graphFibreRange f u v) := by
  by_cases hne : (graphFibreRange f u v).Nonempty
  · rw [rvIsoLift_graphFibreRange_eq_fibre_of_nonempty e.iso f hf hlabel u v hne]
    exact measuredRVLift_fibre_isClopen hv V v
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isClopen_empty

end DiamondIntegral.Section6
