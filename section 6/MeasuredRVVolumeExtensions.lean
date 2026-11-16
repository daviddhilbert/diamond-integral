import «section 6».MeasuredRVLocalFactorizations
import «section 6».RVGlobalVolumeChanges

/-! Extend local finite volumes to a fixed global label domain. The
local labels may be carried by any definable injection. The old volume
is retained off the chosen piece, and total weight is retained globally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def measuredRVVolumeExtension (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D V.object.domain)
    (hχ : Function.Injective χ) : MeasuredRVObject (M := M) S n :=
  U.withVolume hc (replaceMapOn (V.object.volume.comp χ) U.object.volume)
    (replaceMapOn_finiteFibres _ _ (V.finiteVolume.comp (Map.finiteFibres_of_injective hχ)) U.finiteVolume)
    (rvGlobalVolumeChange_nonzero U.object (V.object.volume.comp χ) U.nonzero (fun u k => V.nonzero (χ u) k))

theorem measuredRVVolumeExtension_of_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D V.object.domain)
    (hχ : Function.Injective χ) (u : U.object.domain) (hu : u.val ∈ D.carrier) :
    (measuredRVVolumeExtension hc U V D χ hχ).object.value u = V.object.value (χ ⟨u.val,hu⟩) := by
  change (replaceMapOn (V.object.volume.comp χ) U.object.volume u).val = _
  rw [replaceMapOn_of_mem _ _ u hu]
  rfl

theorem measuredRVVolumeExtension_of_not_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D V.object.domain)
    (hχ : Function.Injective χ) (u : U.object.domain) (hu : u.val ∉ D.carrier) :
    (measuredRVVolumeExtension hc U V D χ hχ).object.value u = U.object.value u := by
  change (replaceMapOn (V.object.volume.comp χ) U.object.volume u).val = _
  rw [replaceMapOn_of_not_mem _ _ u hu]
  rfl

theorem measuredRVVolumeExtension_totalWeight (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D V.object.domain)
    (hχ : Function.Injective χ) (u : U.object.domain) :
    (measuredRVVolumeExtension hc U V D χ hχ).totalWeight u = U.totalWeight u :=
  U.withVolume_totalWeight hc _ _ _ u

theorem measuredRVVolumeExtension_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D V.object.domain)
    (hχ : Function.Injective χ) (hU : U.doublyBounded) (hV : V.doublyBounded) :
    (measuredRVVolumeExtension hc U V D χ hχ).doublyBounded := by
  apply rvGlobalVolumeChange_doublyBounded U.object (V.object.volume.comp χ) hU
  obtain ⟨γ,hγ⟩ := hV.2
  refine ⟨γ,?_⟩
  rintro t ⟨u,rfl⟩ k
  exact hγ (V.object.value (χ u)) ⟨χ u,rfl⟩ k

def measuredRVVolumeExtensionIso (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {V W : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso V W)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D V.object.domain)
    (hχ : Function.Injective χ) :
    MeasuredRVIso (measuredRVVolumeExtension hc U V D χ hχ)
      (measuredRVVolumeExtension hc U W D (e.iso.hom.map.comp χ) ((rvIso_map_bijective e.iso).1.comp hχ)) := by
  let A := measuredRVVolumeExtension hc U V D χ hχ
  let B := measuredRVVolumeExtension hc U W D (e.iso.hom.map.comp χ) ((rvIso_map_bijective e.iso).1.comp hχ)
  exact ⟨rvIsoOfFiniteVolumeNonzero (Map.id U.object.domain) Function.bijective_id
    A.finiteVolume B.finiteVolume A.nonzero B.nonzero,
    fun u => (measuredRVVolumeExtension_totalWeight hc U V D χ hχ u).trans
      (measuredRVVolumeExtension_totalWeight hc U W D _ _ u).symm⟩

theorem measuredRVVolumeExtensionIso_unary (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {V W : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso V W)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D V.object.domain)
    (hχ : Function.Injective χ) (i : Fin n) (he : RVUnaryRelativeAt e.iso.hom.map i) :
    RVUnaryRelativeAt (measuredRVVolumeExtensionIso hc U e D χ hχ).iso.hom.map i := by
  intro u k hk
  change (measuredRVVolumeExtension hc U W D (e.iso.hom.map.comp χ) _).object.value u k =
    (measuredRVVolumeExtension hc U V D χ hχ).object.value u k
  by_cases hu : u.val ∈ D.carrier
  · rw [measuredRVVolumeExtension_of_mem hc U W D (e.iso.hom.map.comp χ)
      ((rvIso_map_bijective e.iso).1.comp hχ) u hu,
      measuredRVVolumeExtension_of_mem hc U V D χ hχ u hu]
    exact he (χ ⟨u.val,hu⟩) k hk
  · rw [measuredRVVolumeExtension_of_not_mem hc U W D (e.iso.hom.map.comp χ)
      ((rvIso_map_bijective e.iso).1.comp hχ) u hu,
      measuredRVVolumeExtension_of_not_mem hc U V D χ hχ u hu]

end DiamondIntegral.Section6
