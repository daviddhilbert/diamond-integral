import IntegrationSection5.RVProjectionPadding
import IntegrationSection5.FixedVFRVIso
import IntegrationSection5.HeadProjectionPadding
import IntegrationSection5.RVProjectionNormalization
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
variable {S : Set M} {m l k : ℕ} {D : DefSet (M := M) S 1 l} {A : DefSet (M := M) S 1 m}
variable {ρ : Fin m → Fin l}
namespace RVProjectionPadding

def toMap (P : RVProjectionPadding (G := G) D A ρ) : Map D A :=
  Map.mk (fun p => ⟨activeUnaryProjection 0 ρ p.val,by rw [← P.values p]; exact (P.iso.equiv p).property⟩)
    (Map.graph_definable (activeUnaryProjectionMap 0 ρ D))

theorem toMap_eq (P : RVProjectionPadding (G := G) D A ρ) (p : D) : P.toMap p = P.iso.equiv p :=
  Subtype.ext (P.values p).symm

theorem toMap_bijective (P : RVProjectionPadding (G := G) D A ρ) : Function.Bijective P.toMap := by
  constructor
  · intro a b he
    rw [P.toMap_eq,P.toMap_eq] at he
    exact P.iso.equiv.injective he
  · intro a
    refine ⟨P.iso.equiv.symm a,?_⟩
    rw [P.toMap_eq,P.iso.equiv.apply_symm_apply]

theorem toMap_contractible (P : RVProjectionPadding (G := G) D A ρ) : Contractible P.toMap := by
  intro p q he
  rw [P.toMap_eq,P.toMap_eq]
  exact (P.sameRV p q).mpr he

theorem toMap_inverse_contractible (P : RVProjectionPadding (G := G) D A ρ) :
    Contractible (Map.inverse P.toMap P.toMap_bijective) := by
  intro p q he
  apply (P.sameRV _ _).mp
  rw [← P.toMap_eq,← P.toMap_eq,Map.apply_inverse,Map.apply_inverse]
  exact he

theorem toMap_gamma (P : RVProjectionPadding (G := G) D A ρ) :
    GammaGraphDefinable G (pointMapGraph P.toMap) := by
  apply GammaGraphDefinable.congr P.iso.graph
  intro p q
  constructor
  · rintro ⟨a,ha,hq⟩
    exact ⟨a,ha,(congrArg Subtype.val (P.toMap_eq a)).trans hq⟩
  · rintro ⟨a,ha,hq⟩
    exact ⟨a,ha,(congrArg Subtype.val (P.toMap_eq a)).symm.trans hq⟩

theorem rvMap_coordinates (P : RVProjectionPadding (G := G) D A ρ)
    (q : rvObjectDomain (pullbackObject D)) :
    (rvContractionMap P.toMap P.toMap_contractible q).val = q.val ∘ headPaddingProjection ρ := by
  obtain ⟨p,rfl⟩ := rawKeyImage_surjective D q
  rw [rvContractionMap_spec]
  change (rawKeyMap A (P.toMap p)).val = (rawKeyMap D p).val ∘ headPaddingProjection ρ
  rw [rawKeyMap_apply,rawKeyMap_apply]
  funext j
  cases j using Fin.addCases with
  | left j =>
    fin_cases j
    change rv (vfAt (P.toMap p).val 0) =
      Fin.append (fun i : Fin 1 => rv (vfAt p.val i)) p.val.2 (headPaddingProjection ρ (0 : Fin (1+m)))
    have hzero : headPaddingProjection ρ (0 : Fin (1+m)) = 0 :=
      Fin.append_left (fun _ : Fin 1 => 0) (Fin.natAdd 1 ∘ ρ) (0 : Fin 1)
    rw [hzero]
    change rv (vfAt p.val 0) = Fin.append (fun i : Fin 1 => rv (vfAt p.val i)) p.val.2 (0 : Fin (1+l))
    exact (Fin.append_left (fun i : Fin 1 => rv (vfAt p.val i)) p.val.2 (0 : Fin 1)).symm
  | right j =>
    simp only [Fin.append_right,headPaddingProjection,Function.comp_apply]
    rfl

def profileIso (P : RVProjectionPadding (G := G) D A ρ)
    (iD : Fin k → Fin (1+l)) (iA : Fin k → Fin (1+m))
    (hi : ∀ j, headPaddingProjection ρ (iA j) = iD j) :
    GammaRVIso G (selectedVolumeObject (Map.image (rawKeyMap D)) iD)
      (selectedVolumeObject (Map.image (rawKeyMap A)) iA) := by
  apply GammaRVIso.ofVolumePreserving
    (U := selectedVolumeObject (Map.image (rawKeyMap D)) iD)
    (V := selectedVolumeObject (Map.image (rawKeyMap A)) iA)
    (rvContractionMap P.toMap P.toMap_contractible)
    (rvContractionMap_bijective P.toMap P.toMap_bijective P.toMap_contractible P.toMap_inverse_contractible) _
      (gamma_rvContractionMap_graph P.toMap P.toMap_contractible P.toMap_gamma)
  intro q
  change (rvContractionMap P.toMap P.toMap_contractible q).val ∘ iA = q.val ∘ iD
  rw [P.rvMap_coordinates]
  funext j
  exact congrArg q.val (hi j)

end RVProjectionPadding
end IntegrationInACVF.Section5
