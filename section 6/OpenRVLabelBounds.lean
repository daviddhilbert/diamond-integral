import «section 6».OpenRVLabelRadii
import «section 6».UnaryRVGammaVolumes

/-! A definable map from a proper invariant source to nonzero RV
tuples has doubly bounded labels as soon as its fixed-label fibres are
open. The uniform radius is constructed before bounding the labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {D : DefSet (rawMixedSpace (M := M) 0 q) S}

def mixedRVCoordinateMap (A : DefSet (rawMixedSpace (M := M) n r) S) (i : Fin r) :
    Map A (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawMixedSpace (M := M) n r
  let F (z : P.Index → M) : Fin 1 → M := fun _ => z (.inr i)
  have hCode (c : P.domain) : rvValues (fun _ : Fin 1 => (P.decode c).2 i)=F c.val := by
    funext j
    exact congrFun (mixedValues_decode c) (.inr i)
  have hDom (c : P.domain) : F c.val ∈ (rawRVSpace (M := M) 1).domain :=
    ⟨fun _ => (P.decode c).2 i,hCode c⟩
  refine Map.ofCodes A (fun p => fun _ : Fin 1 => p.2 i) F (fun _ => Set.DefinableFun.proj LRV) hDom ?_
  intro c
  exact rvValues_injective ((rvValues_decode ⟨F c.val,hDom c⟩).trans (hCode c).symm)

theorem mixedRVCoordinateMap_value (A : DefSet (rawMixedSpace (M := M) n r) S)
    (i : Fin r) (p : A) : (mixedRVCoordinateMap A i p).val 0=p.val.2 i := rfl

def rvLabelCoordinateGammaMap (τ : Map A D) (i : Fin q) :
    Map A (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (scalarRVGammaMap S).comp ((mixedRVCoordinateMap D i).comp τ)

theorem rvLabelCoordinateGammaMap_value (τ : Map A D) (i : Fin q) (p : A)
    (hNZ : ((τ p).val.2 i).val ≠ iRVZero) :
    (rvLabelCoordinateGammaMap τ i p).val.val=Values.vrv ((τ p).val.2 i) :=
  scalarRVGammaMap_nonzero S ((mixedRVCoordinateMap D i).comp τ p) hNZ

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem open_rv_labels_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (τ : Map A D) (hA : ProperInvariant S A.carrier)
    (hOpen : ∀ u v,IsOpen (graphFibreSource τ u v))
    (hNZ : ∀ p : A,∀ i,((τ p).val.2 i).val ≠ iRVZero) : RVSupportDoublyBounded (mixedMapRange τ) := by
  obtain ⟨ρ,hρ⟩ := open_rv_labels_uniform_radius h00 hc linear hκ hs hv hsmall hΓ τ hA hOpen
  let F i := rvLabelCoordinateGammaMap τ i
  let f i := gammaFormExtension (F i)
  have hConst (i : Fin q) (u) (a) (ha : a ∈ vfFibre A.carrier u) (b) (hb : b ∈ vfFibre A.carrier u)
      (hNear : Congruent (fun _ => ρ) a b) : f i (a,u)=f i (b,u) := by
    let p : A := ⟨(a,u),ha⟩
    let z : A := ⟨(b,u),hb⟩
    have hEq := hρ p z rfl hNear
    change gammaFormExtension (F i) p.val=gammaFormExtension (F i) z.val
    rw [gammaFormExtension_at,gammaFormExtension_at]
    change (scalarRVGammaMap S (mixedRVCoordinateMap D i (τ p))).val=
      (scalarRVGammaMap S (mixedRVCoordinateMap D i (τ z))).val
    rw [hEq]
  have hBounds (i : Fin q) : ∃ γ : Gamma M,∀ p ∈ A.carrier,γ⁻¹ ≤ f i p ∧ f i p ≤ γ :=
    properInvariant_locally_constant_gamma_bounded h00 hc linear hκ hs hv hsmall hΓ hA (f i)
      (gammaFormExtension_graph_definable (F i)) ρ (hConst i)
  let γ (i : Fin q) := (hBounds i).choose
  have hγ (i : Fin q) := (hBounds i).choose_spec
  obtain ⟨δ,hδ⟩ := (Set.finite_range (fun i : Option (Fin q) => i.elim 1 γ)).bddAbove
  have hLe (i : Fin q) : γ i ≤ δ := hδ ⟨some i,rfl⟩
  refine ⟨δ,?_⟩
  rintro y ⟨p,rfl⟩ i
  have hVal : (f i p.val).val=Values.vrv ((τ p).val.2 i) := by
    change (gammaFormExtension (F i) p.val).val=_
    rw [gammaFormExtension_at]
    exact rvLabelCoordinateGammaMap_value τ i p (hNZ p i)
  have hLo : (δ⁻¹).val ≤ ((γ i)⁻¹).val := inv_le_inv' (hLe i)
  have hHi : (γ i).val ≤ δ.val := hLe i
  have hBound := hγ i p.val p.property
  change (δ⁻¹).val ≤ Values.vrv ((τ p).val.2 i) ∧ Values.vrv ((τ p).val.2 i) ≤ δ.val
  rw [← hVal]
  exact ⟨hLo.trans hBound.1,hBound.2.trans hHi⟩

end DiamondIntegral.Section6
