import «section 6».MeasuredFrozenUnaryRVDataPreparation
import «section 6».UnarySynchronizedPreparation

/-! Remark 6.20 (`cons:extra`) in VF-dimension one. Let `f : H → 𝒫(RV^q)` be
a proper covariant function, given by its membership relation
`Rel = {(x, u, t) : t ∈ f(x, u)} ⊆ VF × RV^{r+q}`; proper covariance means
that `Rel` is proper invariant: its VF part is bounded, its RV support is
doubly bounded, and every membership section is clopen. Then the special
covariant preparation of Proposition 6.19 (with its pieces and a Γ-form)
can be chosen so that `f ∘ T⁻¹` is rv-contractible: points of the target with
the same RV coordinates have the same value of `f`.

The proof adds the clause to the unary preparation process, as the remark
suggests: a single radius makes every membership section invariant
(`properInvariant_uniform_named_radius`, applied to `Rel` with its extra
tags), finitely many obstacles control all sections at once
(`exists_unary_obstacles`, applied to `Rel`), and the value-prepared process
carries the membership row `unaryRVDataRow Rel` through every focus step.
No freezing is needed, because proper covariance already gives the uniform
radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r q k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The membership row of a proper invariant relation is constant on discs
of one uniform radius. -/
theorem unaryRVDataRow_uniform_constant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (Rel : DefSet (rawMixedSpace (M := M) 1 (r+q)) S) (hRel : ProperInvariant S Rel.carrier)
    (A : Set (Mixed M 1 r)) :
    ∃ ρ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}} ∧
      ∀ u,∀ a ∈ vfFibre A u,∀ b ∈ vfFibre A u,
        Congruent (fun _ => ρ) a b → unaryRVDataRow Rel (a,u) = unaryRVDataRow Rel (b,u) := by
  obtain ⟨ρ,hρ,_,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hRel
  refine ⟨ρ,hρ,fun u a _ b _ hab => ?_⟩
  ext t
  exact hInv (Fin.append u t) a b hab

/-- Remark 6.20 in VF-dimension one. For a proper covariant powerset-valued
function on `A`, given by its proper invariant membership relation `Rel`,
the special covariant preparation of `A` with its pieces `C` (and the
Γ-form `θ`) can be chosen so that the function is constant on the fibres of
the target over its RV coordinates. -/
theorem remark_6_20_unary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i,(C i).carrier ⊆ A.carrier) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (θ : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin 1 → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension θ (x,u)=γ})
    (Rel : DefSet (rawMixedSpace (M := M) 1 (r+q)) S) (hRel : ProperInvariant S Rel.carrier) :
    ∃ s : ℕ,∃ B : DefSet (rawMixedSpace (M := M) 1 s) S,∃ f : Map A B,
      SynchronizedCentripetalChain (G := G) (Fin k) A B f C ∧
      ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      (∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1) ∧
      (∀ i,SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier) ∧
      (∃ U : UnaryContextLift (G := G) (unarySelfPreparationContext A hA hAD hARV hTag) f
          (Fin.elim0 : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) S),
        FormCompatibleSynchronizedChain (G := G) (Fin 0) A U.target.source U.map Fin.elim0 θ) ∧
      ∀ p z : A,(f p).val.2=(f z).val.2 → unaryRVDataRow Rel p.val=unaryRVDataRow Rel z.val := by
  obtain ⟨ρ,hρ,hConst⟩ := unaryRVDataRow_uniform_constant h00 hc linear hκ hs hv hsmall hΓ Rel hRel A.carrier
  obtain ⟨Q,hQ,hQControl⟩ := exists_unary_obstacles hc hv Rel
  obtain ⟨R,hR,hRControl⟩ := exists_finite_unary_obstacles hc hv C
  let U := Q ∪ R
  have hU : S.Definable₁ LRV (Subtype.val '' (U : Set (VF M))) := by
    change S.Definable₁ LRV (Subtype.val '' ((Q ∪ R : Finset (VF M)) : Set (VF M)))
    rw [Finset.coe_union,Set.image_union]
    exact hQ.union hR
  have hUC (i : Fin k) : UnaryObstacleControl (G := G) U (C i).carrier := by
    intro a ρ' hAvoid x hx y hy u
    exact hRControl i a ρ' (fun z hz => hAvoid z (Finset.mem_union_right Q hz)) x hx y hy u
  let roots := UnaryRootFamily.fromObstacles A U hU
  have hBound (u) : (roots.fibre u).card ≤ U.card := by
    apply Finset.card_le_card
    intro x hx
    exact ((roots.mem_fibre u x).mp hx).2
  have hControl (i) : UnaryRootControl (G := G) roots (C i).carrier :=
    UnaryRootFamily.fromObstacles_control U hU _ (hUC i)
  have hValue : UnaryValueRootControl (G := G) roots (unaryRVDataRow Rel) := by
    intro u a ρ' hAmbient hAvoid x hx y hy
    ext t
    apply hQControl a ρ' ?_ x hx y hy (Fin.append u t)
    intro z hz hzd
    apply hAvoid z _ hzd
    exact (roots.mem_fibre u z).mpr ⟨hAmbient z hzd,Finset.mem_union_left R hz⟩
  let X := unarySelfPreparationContext A hA hAD hARV hTag
  obtain ⟨s,B,f,η,hChain,hB,hBD,hBRV,hBTag,hPieces,H,hPhi,hTransport,hConstant⟩ :=
    UnaryRootFamily.exists_value_prepared_form_compatible_context_process_of_bound
      h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt U.card A roots hA hAD hARV hTag hBound
      ρ hρ (unaryRVDataRow Rel) ∅ hConst hValue C hCA hC hControl X
      (Fin.elim0 : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) S) (fun i => i.elim0) (fun i => i.elim0)
      θ hLevels
  refine ⟨s,B,f,hChain,hB,hBD,hBRV,hBTag,hPieces,⟨H,hPhi⟩,?_⟩
  intro p z he
  exact (hTransport p).symm.trans
    ((hConstant (f p).val (f p).property (f z).val (f z).property he).trans (hTransport z))

end DiamondIntegral.Section6
