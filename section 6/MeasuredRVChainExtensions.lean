import «section 6».MeasuredRVVolumeExtensions

/-! Extend an entire local measured relatively unary chain to the old
global label domain. A definable injection carries the local labels;
the global label map is the identity at every stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_measured_rvChain_extension (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    (T : MeasuredRVUnaryChain S n A B) (D : DefSet (rawRVSpace (M := M) U.object.arity) S) :
    ∀ (χ : Map D A.object.domain) (hχ : Function.Injective χ),
    ∃ L : MeasuredRVUnaryChain S n (measuredRVVolumeExtension hc U A D χ hχ)
        (measuredRVVolumeExtension hc U B D (T.iso.iso.hom.map.comp χ)
          ((rvIso_map_bijective T.iso.iso).1.comp hχ)),
      (∀ u, L.iso.iso.hom.map u = u) ∧ ((U.doublyBounded ∧ T.doublyBounded) → L.doublyBounded) := by
  induction T with
  | identity A =>
    intro χ hχ
    exact ⟨.identity _,fun _ => rfl,fun hB => measuredRVVolumeExtension_doublyBounded hc U A D χ hχ hB.1 hB.2⟩
  | @step A B C i e he T ih =>
    intro χ hχ
    let χ' := e.iso.hom.map.comp χ
    have hχ' : Function.Injective χ' := (rvIso_map_bijective e.iso).1.comp hχ
    obtain ⟨L,hL,hLB⟩ := ih χ' hχ'
    let d := measuredRVVolumeExtensionIso hc U e D χ hχ
    refine ⟨.step i d (measuredRVVolumeExtensionIso_unary hc U e D χ hχ i he) L,
      fun u => hL u,fun hB => ?_⟩
    exact ⟨measuredRVVolumeExtension_doublyBounded hc U A D χ hχ hB.1 hB.2.1,hLB ⟨hB.1,hB.2.2⟩⟩

theorem measuredRVVolumeExtension_value_eq (hc : CanonicalStructure.IsCanonical (M := M))
    (U A : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (hVol : ∀ u : D, A.object.value (χ u) = U.object.value ⟨u.val,hD u.property⟩) (u : U.object.domain) :
    (measuredRVVolumeExtension hc U A D χ hχ).object.value u = U.object.value u := by
  by_cases hu : u.val ∈ D.carrier
  · rw [measuredRVVolumeExtension_of_mem hc U A D χ hχ u hu]
    exact hVol ⟨u.val,hu⟩
  · exact measuredRVVolumeExtension_of_not_mem hc U A D χ hχ u hu

def measuredRVVolumeExtensionInitialIso (hc : CanonicalStructure.IsCanonical (M := M))
    (U A : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (hVol : ∀ u : D, A.object.value (χ u) = U.object.value ⟨u.val,hD u.property⟩) :
    MeasuredRVIso U (measuredRVVolumeExtension hc U A D χ hχ) where
  iso := rvIsoOfVolumePreservingBijection (Map.id U.object.domain) Function.bijective_id
    (measuredRVVolumeExtension_value_eq hc U A D hD χ hχ hVol)
  balance u := (measuredRVVolumeExtension_totalWeight hc U A D χ hχ u).symm

theorem exists_measured_rvChain_extension_from_source (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    (T : MeasuredRVUnaryChain S n A B) (D : DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hD : D.carrier ⊆ U.object.domain.carrier) (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (hVol : ∀ u : D, A.object.value (χ u) = U.object.value ⟨u.val,hD u.property⟩) :
    ∃ L : MeasuredRVUnaryChain S n U
        (measuredRVVolumeExtension hc U B D (T.iso.iso.hom.map.comp χ)
          ((rvIso_map_bijective T.iso.iso).1.comp hχ)),
      (∀ u, L.iso.iso.hom.map u = u) ∧ ((U.doublyBounded ∧ T.doublyBounded) → L.doublyBounded) := by
  obtain ⟨L,hL,hLB⟩ := exists_measured_rvChain_extension hc U T D χ hχ
  let i : Fin n := ⟨0,hn⟩
  let d := measuredRVVolumeExtensionInitialIso hc U A D hD χ hχ hVol
  have hd : RVUnaryRelativeAt d.iso.hom.map i := by
    intro u k hk
    exact congrFun (measuredRVVolumeExtension_value_eq hc U A D hD χ hχ hVol u) k
  exact ⟨.step i d hd L,fun u => hL u,fun hB => ⟨hB.1,hLB hB⟩⟩

end DiamondIntegral.Section6
