import «section 6».OrdinaryFiniteOrbitValues
import «section 6».NamedFiniteVFBounds
import «section 6».NamedPairedBoundaryCoefficients

/-! An original-base named radius strictly dominates every nonzero VF
value in the actual finite ordinary orbit. Individual algebraic centres
are not named. The finite-family positive-choice theorem supplies the
named VF representative, including for RV-parameter centre families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def nonzeroScalarFamily (D : DefSet (rawVFSpace (M := M) 1) S) : Set (VF M) :=
  {a | (fun _ : Fin 1 => a) ∈ D.carrier ∧ a≠0}

theorem nonzeroScalarFamily_finite (D : DefSet (rawVFSpace (M := M) 1) S) (hD : D.carrier.Finite) :
    (nonzeroScalarFamily D).Finite := by
  have hi : Function.Injective (fun a : VF M => fun _ : Fin 1 => a) :=
    fun a b h => congrFun h 0
  exact (hD.preimage hi.injOn).subset (fun _ h => h.1)

theorem nonzeroScalarFamily_definable (D : DefSet (rawVFSpace (M := M) 1) S) :
    S.Definable₁ LRV (Subtype.val '' nonzeroScalarFamily D) := by
  have hD := scalar_vf_defSet_definable D
  have hZero := (vfZeroCode_definable (M := M) S).ofPred_eq
    (show S.DefinableFun LRV (fun z : Fin 1 → M => z 0) from Set.DefinableFun.proj LRV)
  change S.Definable LRV {z : Fin 1 → M | iVFZero=z 0} at hZero
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' nonzeroScalarFamily D}
  convert hD.inter hZero.compl using 1
  ext z
  constructor
  · rintro ⟨a,⟨ha,hNZ⟩,he⟩
    exact ⟨⟨a,ha,he⟩,fun hz => hNZ (Subtype.ext (he.trans hz.symm))⟩
  · rintro ⟨⟨a,ha,he⟩,hNZ⟩
    refine ⟨a,⟨ha,?_⟩,he⟩
    intro hz
    exact hNZ ((congrArg Subtype.val hz).symm.trans he)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem finite_vf_defSet_named_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x≠0 ∧ Valued.v x.val≠1)
    (D : DefSet (rawVFSpace (M := M) 1) S) (hD : D.carrier.Finite) :
    ∃ η : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {η}} ∧
      1<η ∧ ∀ x ∈ D.carrier,x 0≠0 → vfValue (x 0)<η.val := by
  obtain ⟨c,hc0,hcDef,hcPos,hAbove⟩ := exists_named_vf_above_finite_family h00 hc hv
    V hV hVS hSV hnt (nonzeroScalarFamily D) (nonzeroScalarFamily_definable D)
    (nonzeroScalarFamily_finite D hD) (fun _ h => h.2)
  refine ⟨finiteValue c hc0,finiteValue_named c hc0 hcDef,hcPos,fun x hx hNZ => ?_⟩
  apply hAbove
  refine ⟨?_,hNZ⟩
  have he : (fun _ : Fin 1 => x 0)=x := by funext i; fin_cases i; rfl
  exact he.symm ▸ hx

theorem ordinaryChainOrbitValues_named_bound {R : Set M} {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
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
      1<η ∧ ∀ x ∈ (ordinaryChainOrbitValues hc T hT E hEA).carrier,x 0≠0 → vfValue (x 0)<η.val :=
  finite_vf_defSet_named_bound h00 hc hv V hV hVS hSV hnt _
    (ordinaryChainOrbitValues_finite hc hκ hs hsmall T hT E hEA hE)

end DiamondIntegral.Section6
