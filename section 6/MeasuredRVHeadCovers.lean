import «section 6».MixedTupleDifferentiability
import Section9.SimultaneousHeadCover
import Section9.FiniteVolumeDimension

/-! Actual simultaneous finite coordinate heads on a finite original-
base cover. The pieces retain the literal source and target labels,
and both restricted head-volume maps have proved finite fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n k : ℕ}

theorem finiteFibres_of_comp_surjective
    {P Q R : Space LRV M} {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}
    (f : Map A B) (g : Map B C) (hf : Function.Surjective f) (hgf : (g.comp f).FiniteFibres) :
    g.FiniteFibres := by
  intro c
  apply ((hgf c).image f).subset
  intro b hb
  obtain ⟨a,rfl⟩ := hf b
  exact ⟨a,hb,rfl⟩

structure MeasuredRVFiniteHeadPiece {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) (k : ℕ) where
  domain : DefSet (rawRVSpace (M := M) U.object.arity) S
  subset : domain.carrier ⊆ U.object.domain.carrier
  sourceSelect : Fin k ↪ Fin n
  targetSelect : Fin k ↪ Fin n
  sourceFinite : (rvHeadVolume (U.restrict domain subset).object sourceSelect).FiniteFibres
  targetFinite : (rvHeadVolume (V.restrict (e.iso.hom.map.restrict subset).image
    (rvLabelImage_subset e.iso domain subset)).object targetSelect).FiniteFibres

def MeasuredRVFiniteHeadPiece.iso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} {e : MeasuredRVIso U V} (P : MeasuredRVFiniteHeadPiece e k) :=
  measuredRVHeadIso hc (e.restrict P.domain P.subset) P.sourceSelect P.targetSelect P.sourceFinite P.targetFinite

theorem exists_measured_rv_finite_head_cover (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (hkn : k ≤ n)
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) (hDim : rvDim U.object.domain ≤ k) :
    ∃ a b : ℕ, ∃ P : Fin a × Fin b → MeasuredRVFiniteHeadPiece e k,
      ∀ u : U.object.domain, ∃ i, u.val ∈ (P i).domain.carrier := by
  let hex := rvExchangeInput_of_earlier hκ hs h00
  have hU := (rvDim_mapImage_eq_of_finiteFibres hc hex hs hsmall U.object.volume U.finiteVolume).le.trans hDim
  have hVDim : rvDim V.object.domain ≤ k := by
    rw [← rvDim_eq_of_bijective e.iso.hom.map (rvIso_map_bijective e.iso)]
    exact hDim
  have hV := (rvDim_mapImage_eq_of_finiteFibres hc hex hs hsmall V.object.volume V.finiteVolume).le.trans hVDim
  let U₀ : RVFiniteObject (M := M) S n := ⟨U.object,U.finiteVolume⟩
  let V₀ : RVFiniteObject (M := M) S n := ⟨V.object,V.finiteVolume⟩
  let E : U₀ ≅ V₀ := rvFiniteIsoOfAmbient e.iso
  obtain ⟨a,b,D,v,w,hD,hCover,hRows⟩ :=
    exists_simultaneous_finite_head_cover hc hκ hs h00 hsmall hkn E hU hV
  have hFinite (i : Fin a × Fin b)
      (θ : Map U.object.domain (DefSet.univ (rawRVSpace (M := M) k) S))
      (hθ : ∀ x, {u : U.object.domain | u.val ∈ (D i).carrier ∧ (θ u).val = x}.Finite) :
      (θ.restrict (hD i)).FiniteFibres := by
    intro x
    let inc (u : D i) : U.object.domain := ⟨u.val,hD i u.property⟩
    have hInc : Function.Injective inc := fun _ _ h =>
      Subtype.ext (congrArg (fun u : U.object.domain => u.val) h)
    apply ((hθ x.val).preimage hInc.injOn).subset
    intro u hu
    exact ⟨u.property,congrArg Subtype.val hu⟩
  have hSrc (i : Fin a × Fin b) :
      (rvHeadVolume (U.restrict (D i) (hD i)).object (v i)).FiniteFibres :=
    hFinite i (rvHeadVolume U.object (v i)) (fun x => (hRows i x).1)
  have hTgt (i : Fin a × Fin b) :
      (rvHeadVolume (V.restrict (e.iso.hom.map.restrict (hD i)).image
        (rvLabelImage_subset e.iso (D i) (hD i))).object (w i)).FiniteFibres := by
    let Eᵢ := e.restrict (D i) (hD i)
    apply finiteFibres_of_comp_surjective Eᵢ.iso.hom.map _ (rvIso_map_bijective Eᵢ.iso).2
    exact hFinite i ((rvHeadVolume V.object (w i)).comp e.iso.hom.map) (fun x => (hRows i x).2)
  exact ⟨a,b,fun i => ⟨D i,hD i,v i,w i,hSrc i,hTgt i⟩,hCover⟩

end DiamondIntegral.Section6
