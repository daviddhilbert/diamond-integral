import «section 6».NamedOrdinaryOrbitBounds
import «section 6».OrdinaryZeroFreeCoreTranslations

/-! A single original-base named radius dominates the actual maximum
of all finite-word point thresholds for a centre family with finite VF
projection. It therefore works simultaneously before every first zero
event, without naming individual algebraic centres or RV parameters. -/

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

theorem ordinaryChainOrbitValues_head_member {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hEA : E.carrier ⊆ SpecialTransformations.Section5.carrier A) (p : E) :
    p.val.1 ∈ (ordinaryChainOrbitValues hc T hT E hEA).carrier := by
  cases T with
  | nil A => exact ⟨p,rfl⟩
  | cons step tail => exact Or.inl ⟨p,rfl⟩

theorem ordinaryChainPointRadius_lt_of_orbit_bound {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    ∀ (E : DefSet (rawMixedSpace (M := M) 1 r) S)
      (hEA : E.carrier ⊆ SpecialTransformations.Section5.carrier A) (η : Gamma M),
      1<η → (∀ x ∈ (ordinaryChainOrbitValues hc T hT E hEA).carrier,x 0≠0 → vfValue (x 0)<η.val) →
      ∀ p : E,ordinaryChainPointRadius T ⟨p.val,hEA p.property⟩<η := by
  induction T with
  | nil A =>
    intro E hEA η hη hBound p
    have hHead : ordinaryNonzeroFieldValue p.val.1<η := by
      by_cases hn : p.val.1 0≠0
      · simp only [ordinaryNonzeroFieldValue,dif_pos hn]
        exact hBound p.val.1 ⟨p,rfl⟩ hn
      · simp only [ordinaryNonzeroFieldValue,dif_neg hn]
        exact hη
    exact max_lt hη hHead
  | @cons r s t A B C step tail ih =>
    intro E hEA η hη hBound p
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
    have hHead : ordinaryNonzeroFieldValue p.val.1<η := by
      by_cases hn : p.val.1 0≠0
      · simp only [ordinaryNonzeroFieldValue,dif_pos hn]
        exact hBound p.val.1 (Or.inl ⟨p,rfl⟩) hn
      · simp only [ordinaryNonzeroFieldValue,dif_neg hn]
        exact hη
    have hBoundTail : ∀ x ∈ (ordinaryChainOrbitValues hc tail hT.2 f.image hImage).carrier,
        x 0≠0 → vfValue (x 0)<η.val := fun x hx hNZ => hBound x (Or.inr hx) hNZ
    have hTail := ih hT.2 f.image hImage η hη hBoundTail (f.toImage p)
    exact max_lt (max_lt hη hHead) hTail

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

include hc in
theorem ordinaryChainPointRadius_uniform_named_bound {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x≠0 ∧ Valued.v x.val≠1)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hEA : E.carrier ⊆ SpecialTransformations.Section5.carrier A)
    (hE : (Prod.fst '' E.carrier).Finite) :
    ∃ η : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {η}} ∧
      1<η ∧ ∀ p : E,ordinaryChainPointRadius T ⟨p.val,hEA p.property⟩<η := by
  obtain ⟨η,hNamed,hη,hBound⟩ := ordinaryChainOrbitValues_named_bound h00 hc hκ hs hsmall hv
    V hV hVS hSV hnt T hT E hEA hE
  exact ⟨η,hNamed,hη,ordinaryChainPointRadius_lt_of_orbit_bound hc T hT E hEA η hη hBound⟩

end DiamondIntegral.Section6
