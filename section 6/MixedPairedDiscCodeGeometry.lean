import «section 6».MixedScalarGraphWitnesses
import «section 6».ParameterizedPairedDiscCodes
import «section 6».PairedDiscImageGeometry

/-! The uniform paired mixed-disc formula is exactly the actual
whole-disc image equality on fixed old source and target RV labels.
All arbitrary raw codes are interpreted through actual graph witnesses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s n : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem unaryMixedScalarGraph_scalar_fibre (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (z : Fin 2 → M) :
    Sum.elim (rvValues (Fin.append u v)) z ∈ unaryMixedScalarGraph f ↔
      z ∈ scalarPartialGraph (unaryGraphFibreSource f u v) (unaryGraphFibreMap f u v) := by
  have hEta : ![z 0,z 1]=z := by funext i; fin_cases i <;> rfl
  constructor
  · intro hz
    rw [← hEta] at hz
    obtain ⟨p,hpa,hpb,hpu,hpv⟩ := (unaryMixedScalarGraph_raw_scalars f u v (z 0) (z 1)).mp hz
    have hpSource : p.val.1 0 ∈ unaryGraphFibreSource f u v := by
      simpa only [hpu,hpv] using unaryGraphFibreSource_at f p
    have hpMap : unaryGraphFibreMap f u v (p.val.1 0)=(f p).val.1 0 := by
      simpa only [hpu,hpv] using unaryGraphFibreMap_at f p
    refine ⟨p.val.1 0,hpSource,hpa,?_⟩
    rw [hpMap]
    exact hpb
  · rintro ⟨x,hx,hxz,hgz⟩
    obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph f u v hx
    have hpField : p.val.1 0=x := congrArg (fun q : Mixed M 1 r => q.1 0) hp
    have hfpField : (f p).val.1 0=unaryGraphFibreMap f u v x := congrArg (fun q : Mixed M 1 s => q.1 0) hfp
    have hpu := congrArg (fun q : Mixed M 1 r => q.2) hp
    have hpv := congrArg (fun q : Mixed M 1 s => q.2) hfp
    rw [← hEta]
    apply (unaryMixedScalarGraph_raw_scalars f u v (z 0) (z 1)).mpr
    exact ⟨p,(congrArg Subtype.val hpField).trans hxz,(congrArg Subtype.val hfpField).trans hgz,hpu,hpv⟩

theorem scalar_partial_graph_raw_domain_iff (D : Set (VF M)) (g : VF M → VF M) (x : M) :
    (∃ y : Fin 1 → M,![x,y 0] ∈ scalarPartialGraph D g) ↔ x ∈ Subtype.val '' D := by
  constructor
  · rintro ⟨y,p,hp,hpx,hpy⟩
    exact ⟨p,hp,hpx⟩
  · rintro ⟨p,hp,hpx⟩
    exact ⟨fun _ => (g p).val,p,hp,hpx,rfl⟩

theorem parameterizedPairedDiscCodes_scalar_fibre
    (G : Set (Fin n ⊕ Fin 2 → M)) (t : Fin n → M) (D : Set (VF M)) (g : VF M → VF M)
    (hFibre : ∀ z : Fin 2 → M,Sum.elim t z ∈ G ↔ z ∈ scalarPartialGraph D g) (z : Fin 4 → M) :
    Sum.elim t z ∈ parameterizedPairedDiscCodes G ↔ z ∈ pairedDiscImageCodes D g := by
  simp only [parameterizedPairedDiscCodes,pairedDiscImageCodes,Set.mem_setOf_eq,
    Function.comp_def,Sum.elim_inl,Sum.elim_inr]
  simp_rw [hFibre,scalar_partial_graph_raw_domain_iff]

theorem mixedPairedDiscCodes_at (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (a b d e : VF M) (hd : d ≠ 0) (he : e ≠ 0) :
    Sum.elim (rvValues (Fin.append u v)) ![a.val,b.val,d.val,e.val] ∈
        parameterizedPairedDiscCodes (unaryMixedScalarGraph f) ↔
      a ∈ unaryGraphFibreSource f u v ∧ unaryGraphFibreMap f u v a=b ∧
      centeredGammaDisc a (finiteValue d hd) ⊆ unaryGraphFibreSource f u v ∧
      unaryGraphFibreMap f u v '' centeredGammaDisc a (finiteValue d hd)=
        centeredGammaDisc b (finiteValue e he) :=
  (parameterizedPairedDiscCodes_scalar_fibre (unaryMixedScalarGraph f) (rvValues (Fin.append u v))
    (unaryGraphFibreSource f u v) (unaryGraphFibreMap f u v) (unaryMixedScalarGraph_scalar_fibre f u v) _).trans
    (pairedDiscImageCodes_at _ _ a b d e hd he)

end DiamondIntegral.Section6
