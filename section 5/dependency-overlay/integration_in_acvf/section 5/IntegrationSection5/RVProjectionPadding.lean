import IntegrationSection5.GammaCoordinateCanonical
import IntegrationSection5.CanonicalRVSliceGeometry
import IntegrationSection5.HeadIsoRVKernel
import IntegrationSection5.CanonicalUnaryBranchExtension
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m l : ℕ} {D : DefSet (M := M) S 1 l} {A : DefSet (M := M) S 1 m}

structure RVProjectionPadding (D : DefSet (M := M) S 1 l) (A : DefSet (M := M) S 1 m)
    (ρ : Fin m → Fin l) where
  iso : GammaIso G (carrier D) (carrier A)
  values : ∀ p : D, (iso.equiv p).val = activeUnaryProjection 0 ρ p.val
  sameRV : ∀ p q : D, SameRV (iso.equiv p).val (iso.equiv q).val ↔ SameRV p.val q.val

def paddingRVLabels (D : DefSet (M := M) S 1 l) : Set (Fin l → RV (M := M)) :=
  {s | ∃ p ∈ carrier D, p.2 = s}

namespace RVProjectionPadding
variable {ρ : Fin m → Fin l}

theorem product_source (P : RVProjectionPadding (G := G) D A ρ)
    (hClass : ∀ p ∈ carrier A, ∀ q ∈ carrier A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    carrier D = {p | activeUnaryProjection 0 ρ p ∈ carrier A ∧ p.2 ∈ paddingRVLabels D} := by
  ext p
  constructor
  · intro hp
    have hm := (P.iso.equiv ⟨p,hp⟩).property
    rw [P.values] at hm
    exact ⟨hm,⟨p,hp,rfl⟩⟩
  · rintro ⟨hA,d,hd,hLabels⟩
    let a : A := ⟨activeUnaryProjection 0 ρ p,hA⟩
    let dp : D := P.iso.equiv.symm a
    let de : D := ⟨d,hd⟩
    have hdp : (P.iso.equiv dp).val = a.val := congrArg Subtype.val (P.iso.equiv.apply_symm_apply a)
    have hde : (P.iso.equiv de).val.2 = a.val.2 := by
      rw [P.values]
      exact congrArg (fun s => s ∘ ρ) hLabels
    have he : SameRV (P.iso.equiv dp).val (P.iso.equiv de).val := by
      rw [hdp]
      apply (sameRV_iff _ _).mpr
      refine ⟨fun i => ?_,hde.symm⟩
      fin_cases i
      exact hClass a.val a.property (P.iso.equiv de).val (P.iso.equiv de).property hde.symm
    have hSame := (P.sameRV dp de).mp he
    have hRV : dp.val.2 = p.2 := ((sameRV_iff _ _).mp hSame).2.trans hLabels
    have hVF : dp.val.1 = p.1 := by
      have hpv := (P.values dp).symm.trans hdp
      funext i; fin_cases i
      exact congrArg (fun z : Point (M := M) 1 m => vfAt z 0) hpv
    exact (Prod.ext hVF hRV) ▸ dp.property

theorem canonical_sameRV_iff (p q : Point (M := M) 1 l) :
    SameRV (coordinateCanonical 0 p) (coordinateCanonical 0 q) ↔ SameRV p q := by
  constructor
  · intro h
    have he := activeUnaryProjection_sameRV 0 (Fin.natAdd 1) h
    rw [activeUnaryProjection_dropCanonical,activeUnaryProjection_dropCanonical,
      activeUnaryProjection_one_id,activeUnaryProjection_one_id] at he
    exact he
  · exact coordinateCanonical_sameRV 0

def canonical (P : RVProjectionPadding (G := G) D A ρ) :
    RVProjectionPadding (G := G) (coordinateCanonicalImage D 0) A (Fin.natAdd 1 ∘ ρ) := by
  let can := coordinateCanonicalGammaIso D ((P.iso.symm (gammaLogicInput G)).target_definable (gammaLogicInput G)) 0
  let e := (can.symm (gammaLogicInput G)).trans (gammaLogicInput G) P.iso
  refine ⟨e,?_,?_⟩
  · intro p
    obtain ⟨d,rfl⟩ := can.equiv.surjective p
    change (P.iso.equiv (can.equiv.symm (can.equiv d))).val = _
    rw [can.equiv.symm_apply_apply,P.values]
    apply Prod.ext
    · rfl
    · funext j
      change d.val.2 (ρ j) = (coordinateCanonical 0 d.val).2 (Fin.natAdd 1 (ρ j))
      exact (Fin.append_right (fun _ : Fin 1 => rv (vfAt d.val 0)) d.val.2 (ρ j)).symm
  · intro p q
    obtain ⟨d,rfl⟩ := can.equiv.surjective p
    obtain ⟨a,rfl⟩ := can.equiv.surjective q
    change SameRV (P.iso.equiv (can.equiv.symm (can.equiv d))).val
      (P.iso.equiv (can.equiv.symm (can.equiv a))).val ↔ _
    rw [can.equiv.symm_apply_apply,can.equiv.symm_apply_apply,P.sameRV]
    exact (canonical_sameRV_iff d.val a.val).symm

end RVProjectionPadding
end IntegrationInACVF.Section5
