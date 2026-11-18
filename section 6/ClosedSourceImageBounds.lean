import «section 6».OpenRVLabelGeometry
import «section 6».ClopenCriterion
import «section 6».InvarianceTopology
import «section 6».ProperCovariance

/-! Remark 6.4: for a closed source, the double boundedness of the image
RV coordinates in Definition 6.2 follows from the remaining conditions.

Correction approved by the author: "doubly bounded" excludes the RV value
`∞`, so the image RV coordinates must be nonzero. Without this the remark
fails: on `A = 𝒪 × {1}` the map `(a,1) ↦ (a,0)` satisfies every other
condition (each VF-fiber is the identity of `𝒪`), but `f(A)_RV = {0}` is not
doubly bounded. The nonzero hypothesis is the only addition. Closedness is
used fiberwise, which is what the argument needs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

omit [M ⊨ Axioms.ACVF] in
/-- Each source tag fiber is the union of the graph-fiber sources over the
target tags. -/
theorem vfFibre_eq_iUnion_graphFibreSource (f : Map A B) (u : Fin r → RVInfinity M) :
    vfFibre A.carrier u = ⋃ v, graphFibreSource f u v := by
  ext a
  simp only [Set.mem_iUnion]
  constructor
  · intro ha
    let p : A := ⟨(a,u),ha⟩
    exact ⟨(f p).val.2,(f p).val.1,p,rfl,rfl⟩
  · rintro ⟨v,b,p,hp,_⟩
    change (a,u) ∈ A.carrier
    exact hp ▸ p.property

/-- The covariance clause of Definition 6.2, without the global bounds. -/
def CovariantRadii (f : Map A B) : Prop :=
  ∀ u : Fin r → RVInfinity M, ∀ v : Fin s → RVInfinity M,
    ∃ α : Fin n → Gamma M, ∃ β : Fin m → Gamma M,
      NamedGammaTuple (graphFibreBase S u v) α ∧
      NamedGammaTuple (graphFibreBase S u v) β ∧
      AlphaInvariant α (graphFibreSource f u v) ∧
      AlphaInvariant β (graphFibreRange f u v) ∧
      AlphaBetaCovariant α β (graphFibreSource f u v) (graphFibreMap f u v)

/-- Remark 6.4 (with nonzero image RV coordinates). If the source fibers
are closed, the source is VF-bounded with doubly bounded RV part and the
covariance clause holds, then the image RV coordinates are doubly bounded. -/
theorem remark_6_4
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hVF : VFBounded A.carrier) (hRV : RVSupportDoublyBounded A.carrier)
    (hclosed : ∀ u, IsClosed (vfFibre A.carrier u)) (hradii : CovariantRadii f)
    (hNZ : ∀ p : A, ∀ i, ((f p).val.2 i).val ≠ iRVZero) :
    RVSupportDoublyBounded (mixedMapRange f) := by
  have hOpen (u v) : IsOpen (graphFibreSource f u v) := by
    obtain ⟨α,β,_,_,hD,_,_⟩ := hradii u v
    exact hD.isOpen hv
  have hA : ProperInvariant S A.carrier :=
    (lemma_6_5 h00 hc hκ hs hv A.carrier A.definable hVF hRV).mpr (fun u =>
      ⟨hclosed u,by rw [vfFibre_eq_iUnion_graphFibreSource f u]; exact isOpen_iUnion (hOpen u)⟩)
  have hSurj : Function.Surjective f.toImage := by
    rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩
  exact target_rvBounded_of_open_nonzero_labels h00 hc linear hκ hs hv hsmall hΓ f.toImage hSurj hA
    (fun u v => hOpen u v) hNZ

/-- Remark 6.4, packaged: under the same hypotheses, `f` is proper
covariant once its image is VF-bounded. -/
theorem remark_6_4_properCovariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hVF : VFBounded A.carrier) (hRV : RVSupportDoublyBounded A.carrier)
    (himage : VFBounded (mixedMapRange f))
    (hclosed : ∀ u, IsClosed (vfFibre A.carrier u)) (hradii : CovariantRadii f)
    (hNZ : ∀ p : A, ∀ i, ((f p).val.2 i).val ≠ iRVZero) : ProperCovariant f :=
  ⟨hVF,himage,hRV,remark_6_4 h00 hc linear hκ hs hv hsmall hΓ f hVF hRV hclosed hradii hNZ,hradii⟩

end DiamondIntegral.Section6
