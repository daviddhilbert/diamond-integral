import «section 6».PairedCoreMatching

/-! Paired whole-core matching survives the actual whole-ambient
preparations and agrees with the restriction of their global conjugate.
Thus no independently defined core permutation is substituted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.AmbientCorePreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {U : UnaryFocusData A} {V : UnaryFocusData B}
variable {dMap : Map (focusActive A U.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {eMap : Map (focusActive B V.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable (F : AmbientCorePreparation (G := G) U dMap) (H : AmbientCorePreparation (G := G) V eMap)

def coreMap := (F.map.restrict (U.offsetCoreDomain_subset dMap)).toImage

theorem coreMap_bijective : Function.Bijective F.coreMap :=
  restrict_toImage_bijective F.map F.bijective.injective (U.offsetCoreDomain_subset dMap)

def coreConjugate (g : Map (U.offsetCoreDomain dMap) (V.offsetCoreDomain eMap)) :
    Map F.coreMap.image H.coreMap.image :=
  H.coreMap.comp (g.comp (F.coreMap.inverse F.coreMap_bijective))

theorem coreConjugate_at (g : Map (U.offsetCoreDomain dMap) (V.offsetCoreDomain eMap))
    (p : U.offsetCoreDomain dMap) : F.coreConjugate H g (F.coreMap p)=H.coreMap (g p) := by
  change H.coreMap (g (F.coreMap.inverse _ (F.coreMap p)))=H.coreMap (g p)
  rw [Map.inverse_apply]

theorem coreConjugate_whole_fibres (g : Map (U.offsetCoreDomain dMap) (V.offsetCoreDomain eMap))
    (hg : Function.Bijective g) (hWhole : MapsWholeTagFibres g) : MapsWholeTagFibres (F.coreConjugate H g) :=
  hWhole.conjugate g hg F.coreMap F.coreMap_bijective H.coreMap H.coreMap_bijective F.coreLabels H.coreLabels

theorem coreConjugate_bijective (g : Map (U.offsetCoreDomain dMap) (V.offsetCoreDomain eMap))
    (hg : Function.Bijective g) : Function.Bijective (F.coreConjugate H g) := by
  have hInv : Function.Bijective (F.coreMap.inverse F.coreMap_bijective) := by
    constructor
    · intro p q he
      have hh := congrArg F.coreMap he
      simpa only [Map.apply_inverse] using hh
    · intro p
      exact ⟨F.coreMap p,Map.inverse_apply F.coreMap F.coreMap_bijective p⟩
  exact H.coreMap_bijective.comp (hg.comp hInv)

def wholeConjugate (f : Map A B) : Map F.target H.target :=
  H.map.comp (f.comp (F.map.inverse F.bijective))

theorem wholeConjugate_at (f : Map A B) (p : A) :
    F.wholeConjugate H f (F.map p)=H.map (f p) := by
  change H.map (f (F.map.inverse _ (F.map p)))=H.map (f p)
  rw [Map.inverse_apply]

theorem wholeConjugate_agrees_on_core (f : Map A B)
    (g : Map (U.offsetCoreDomain dMap) (V.offsetCoreDomain eMap))
    (hCommutes : ∀ p : U.offsetCoreDomain dMap,
      (g p).val=(f ⟨p.val,U.offsetCoreDomain_subset dMap p.property⟩).val)
    (p : U.offsetCoreDomain dMap) :
    (F.wholeConjugate H f (F.map ⟨p.val,U.offsetCoreDomain_subset dMap p.property⟩)).val=
      (F.coreConjugate H g (F.coreMap p)).val := by
  rw [F.wholeConjugate_at H f,F.coreConjugate_at H g]
  change (H.map (f ⟨p.val,U.offsetCoreDomain_subset dMap p.property⟩)).val=
    (H.map ⟨(g p).val,V.offsetCoreDomain_subset eMap (g p).property⟩).val
  have hB : f ⟨p.val,U.offsetCoreDomain_subset dMap p.property⟩=
      ⟨(g p).val,V.offsetCoreDomain_subset eMap (g p).property⟩ := Subtype.ext (hCommutes p).symm
  rw [hB]

end DiamondIntegral.Section6.AmbientCorePreparation
