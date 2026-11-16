import «section 6».OriginalBaseOrdinaryMatching
import «section 6».UnaryFiniteFieldImages
import «section 6».MixedVFProjectionMaps

/-! All VF values of an actual finite ordinary unary word on a centre
family form one original-base definable finite VF set. Only finite VF
projection is needed; arbitrary retained RV fibres are allowed. This
supplies uniform nonzero-trajectory thresholds before first zero events. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M}
variable (hc : CanonicalStructure.IsCanonical (M := M))

def ordinaryChainOrbitValues : {r s : ℕ} →
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r} →
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} →
    (T : SpecialTransformations.Section5.Chain R 1 A B) →
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) →
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) →
    (E.carrier ⊆ SpecialTransformations.Section5.carrier A) → DefSet (rawVFSpace (M := M) 1) S
  | _,_,_,_,.nil _,_,E,_ => (mixedVFHeadMap E).image
  | _,_,_,_,.cons step tail,hT,E,hE => by
      let P := ordinaryNamedGammaBase S
      let L := SpecialTransformations.Section5.gammaLogicInput P
      let hSource := SpecialTransformations.Section5.GammaChainDefinable.source P (.cons step tail) hT
      let hTarget := SpecialTransformations.Section5.GammaChainDefinable.source P tail hT.2
      let f := (originalBaseOrdinaryMap hc hSource hTarget step.toMap
        (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph L step hT.1)).comp
          (Map.inclusion hE)
      let hImage : f.image.carrier ⊆ _ := fun q hq => by
        obtain ⟨p,rfl⟩ := hq
        exact (f p).property
      let H := (mixedVFHeadMap E).image
      let K := ordinaryChainOrbitValues tail hT.2 f.image hImage
      exact ⟨H.carrier ∪ K.carrier,H.definable.union _ K.definable⟩

theorem mixedVFHeadImage_finite {r : ℕ} (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hE : (Prod.fst '' E.carrier).Finite) : (mixedVFHeadMap E).image.carrier.Finite := by
  apply hE.subset
  rintro x ⟨p,hp⟩
  exact ⟨p.val,p.property,hp⟩

theorem ordinaryChainOrbitValues_finite {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    ∀ (E : DefSet (rawMixedSpace (M := M) 1 r) S)
      (hE : E.carrier ⊆ SpecialTransformations.Section5.carrier A),
      (Prod.fst '' E.carrier).Finite → (ordinaryChainOrbitValues hc T hT E hE).carrier.Finite := by
  induction T with
  | nil A => exact fun E _ hE => mixedVFHeadImage_finite E hE
  | @cons r s t A B C step tail ih =>
    intro E hEA hE
    let P := ordinaryNamedGammaBase S
    let L := SpecialTransformations.Section5.gammaLogicInput P
    let hSource := SpecialTransformations.Section5.GammaChainDefinable.source P (.cons step tail) hT
    let hTarget := SpecialTransformations.Section5.GammaChainDefinable.source P tail hT.2
    let f := (originalBaseOrdinaryMap hc hSource hTarget step.toMap
      (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph L step hT.1)).comp
        (Map.inclusion hEA)
    let hImage : f.image.carrier ⊆ SpecialTransformations.Section5.carrier B := fun q hq => by
      obtain ⟨p,rfl⟩ := hq
      exact (f p).property
    have hFin : (Prod.fst '' f.image.carrier).Finite := by
      apply (unaryFieldImage_finite hc hκ hs hsmall f E.carrier hE).subset
      rintro x ⟨q,⟨p,hp⟩,rfl⟩
      exact ⟨p,p.property,congrArg Prod.fst hp⟩
    exact (mixedVFHeadImage_finite E hE).union (ih hT.2 f.image hImage hFin)

theorem ordinaryChainOrbitValues_nonzero_bound {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hEA : E.carrier ⊆ SpecialTransformations.Section5.carrier A)
    (hE : (Prod.fst '' E.carrier).Finite) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ x ∈ (ordinaryChainOrbitValues hc T hT E hEA).carrier,
      x 0≠0 → vfValue (x 0) ≤ η.val := by
  let val (x : Fin 1 → VF M) : Gamma M := if hx : x 0≠0 then finiteValue (x 0) hx else 1
  obtain ⟨β,hβ⟩ := ((ordinaryChainOrbitValues_finite hc hκ hs hsmall T hT E hEA hE).image val).bddAbove
  refine ⟨max β 1,le_max_right _ _,fun x hx hNZ => ?_⟩
  have h := hβ (Set.mem_image_of_mem val hx)
  have he : val x=finiteValue (x 0) hNZ := by simp only [val,dif_pos hNZ]
  rw [he] at h
  exact h.trans (le_max_left _ _)

end DiamondIntegral.Section6
