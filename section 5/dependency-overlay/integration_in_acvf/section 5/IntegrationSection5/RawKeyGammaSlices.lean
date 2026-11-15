import IntegrationSection5.RVContractionGamma
import IntegrationSection5.GammaSurjectiveRVComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
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
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {S : Set M} {n m l : ℕ}
variable {X : DefSet (M := M) S n m} {Y : DefSet (M := M) S 1 l}

theorem gamma_rawKey_output (f : Map X Y) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (rvOutputGraph (Map.comp (Map.toImage (rawKeyMap Y)) f)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).comp_graph hf
    ((gammaLogicInput G).real_map_graph (mixedKeyPointMap G.real 1 l)))
  intro p q
  constructor
  · rintro ⟨w,⟨a,ha,hf⟩,⟨z,hz,hq⟩⟩
    change mixedKeyPoint z.val = q at hq
    have he : z.val = (f a).val := hz.trans hf.symm
    rw [he] at hq
    exact ⟨a,ha,(rawKeyMap_apply Y (f a)).trans (congrArg Prod.snd hq)⟩
  · rintro ⟨a,ha,hq⟩
    refine ⟨(f a).val,⟨a,ha,rfl⟩,⟨(f a).val,Set.mem_univ _⟩,rfl,?_⟩
    change mixedKeyPoint (f a).val = q
    exact Prod.ext (Subsingleton.elim _ _) ((rawKeyMap_apply Y (f a)).symm.trans hq)

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {S : Set M} {n m r : ℕ}
variable {X : DefSet (M := M) S n m} {Y : PresentedSet (rawRVSpace (M := M) r) S}

theorem gamma_rawOutput_target (f : Map X Y) (hf : Function.Surjective f)
    (hG : GammaGraphDefinable G (rvOutputGraph f)) :
    GammaSetDefinable G {q : Point (M := M) 0 r | q.2 ∈ carrier Y} := by
  have h := (gammaLogicInput G).image_graph hG
  have he : {q | ∃ p, rvOutputGraph f p q} = {q : Point (M := M) 0 r | q.2 ∈ carrier Y} := by
    ext q
    constructor
    · rintro ⟨p,a,ha,hq⟩
      change q.2 ∈ carrier Y
      rw [← hq]
      exact (f a).property
    · intro hq
      obtain ⟨a,ha⟩ := hf ⟨q.2,hq⟩
      exact ⟨a.val,a,rfl,congrArg (fun z : Y => z.val) ha⟩
  exact he ▸ h

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m a : ℕ} {D Y : DefSet (M := M) S n m}

theorem rawKeyMap_oldLabels (Y : DefSet (M := M) S n m) (p : Y) :
    (rawKeyMap Y p).val ∘ Fin.natAdd n = p.val.2 := by
  funext j
  rw [rawKeyMap_apply]
  exact Fin.append_right (fun i : Fin n => rv (vfAt p.val i)) p.val.2 j

theorem rawKeyImage_rvSlice (ρ : Fin a → Fin m) (E : Set (Fin a → RV (M := M)))
    (hD : carrier D = {p | p ∈ carrier Y ∧ p.2 ∘ ρ ∈ E}) :
    carrier (Map.image (rawKeyMap D)) = {q | q ∈ carrier (Map.image (rawKeyMap Y)) ∧ q ∘ (Fin.natAdd n ∘ ρ) ∈ E} := by
  ext q
  constructor
  · rintro ⟨d,hd⟩
    have hdy := ((Set.ext_iff.mp hD d.val).mp d.property).1
    let y : Y := ⟨d.val,hdy⟩
    have hy : (rawKeyMap Y y).val = q := (rawKeyMap_apply Y y).trans ((rawKeyMap_apply D d).symm.trans hd)
    refine ⟨⟨y,hy⟩,?_⟩
    rw [← hy]
    change ((rawKeyMap Y y).val ∘ Fin.natAdd n) ∘ ρ ∈ E
    rw [rawKeyMap_oldLabels]
    exact ((Set.ext_iff.mp hD d.val).mp d.property).2
  · rintro ⟨⟨y,hy⟩,he⟩
    change (rawKeyMap Y y).val = q at hy
    have hFlag : y.val.2 ∘ ρ ∈ E := by
      have hl := congrArg (fun s => s ∘ ρ) (rawKeyMap_oldLabels Y y)
      change (rawKeyMap Y y).val ∘ (Fin.natAdd n ∘ ρ) = y.val.2 ∘ ρ at hl
      rw [← hl,hy]
      exact he
    let d : D := ⟨y.val,(Set.ext_iff.mp hD y.val).mpr ⟨y.property,hFlag⟩⟩
    exact ⟨d,(rawKeyMap_apply D d).trans ((rawKeyMap_apply Y y).symm.trans hy)⟩

end IntegrationInACVF.Section5
