import «section 3».GammaSelectedRawEndpointComparison
import «section 3».GammaNativeSelectedTotalRows
import «section 3».GammaNativeEndpointHeterogeneousSpecs
import «section 3».GammaSelectedNativeFinalComparison
import IntegrationSection6.RawFiniteContractions
import IntegrationSection6.FiniteContractionLabels

/-! The native ordered endpoint has the principal class of the literal
raw standard contraction, with its original retained Gamma form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hg : Cardinal.mk B.gamma < C.κ) {n a : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
variable {σ : Equiv.Perm (Fin (n+1))}

theorem gammaPositive_tail_raw_value
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    {m c k : ℕ}
    {H : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) m c}
    (P : OrderedContractionProgram (C.base : Set M) H T.target)
    (hP : GammaProgramDefinable B P) (hH : GammaSetDefinable B (carrier H))
    (ρ : Fin (k+1) → Fin c) (hfinH : ∀ x t, {r | (x,r) ∈ carrier H ∧ r ∘ ρ = t}.Finite)
    (ℓ : Fin a → Fin c)
    (U : GammaSelectedRetainedData hc B 0 (n+1))
    (hd : n+1 = orderedVolumeDegree m (k+1))
    (hU : HEq U (gammaNativeOrderedEndpoint C hBC hv P hP hH ρ hfinH
      (GammaGroundDefSet.univ hc B (rawRVSpace c)) (fun _ => Set.mem_univ _)
      (gammaTotalRVCoordinateForm ℓ ω)))
    (hProduct : ∀ w : Fin T.arity → Values.GammaTop (M := M),
      (∏ i, w (P.volumeIndex i)) * (∏ j, w (suffixIndex P.rvArity_le (ρ j))) =
        ∏ i, w (T.volumeIndex i))
    (hLabels : ∀ i, suffixIndex P.rvArity_le (ℓ i) = suffixIndex T.program.rvArity_le i) :
    U.finalValue C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hg =
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfin T hT ω) := by
  let E := gammaNativeOrderedEndpoint C hBC hv P hP hH ρ hfinH
    (GammaGroundDefSet.univ hc B (rawRVSpace c)) (fun _ => Set.mem_univ _)
    (gammaTotalRVCoordinateForm ℓ ω)
  have hspec := gammaNativeOrderedEndpoint_spec C hBC hv P hP hH ρ hfinH
    (GammaGroundDefSet.univ hc B (rawRVSpace c)) (fun _ => Set.mem_univ _)
    (gammaTotalRVCoordinateForm ℓ ω)
  have ha : U.arity = T.arity := (gammaSelectedData_heq_arity hd hU).trans hspec.1
  have hset : HEq U.set (extendBase T.target (Set.subset_univ _)) :=
    (gammaSelectedData_heq_set hd hU).trans hspec.2.1
  have hsel : HEq U.select (orderedSelectedIndex P ρ) :=
    (gammaSelectedData_heq_select hd hU).trans hspec.2.2
  rcases U with ⟨b,X,hX,ι,hfinite,Q,hQ,η⟩
  dsimp only at ha hset
  subst b
  have hXeq : X = extendBase T.target (Set.subset_univ _) := eq_of_heq hset
  subst X
  let U : GammaSelectedRetainedData hc B 0 (n+1) :=
    ⟨T.arity,extendBase T.target (Set.subset_univ _),hX,ι,hfinite,Q,hQ,η⟩
  apply gammaSelected_raw_endpoint_comparison C hBC hg hA hfin T hT ω U rfl HEq.rfl
  · intro r s hrs
    have hrs' : r = s := eq_of_heq hrs
    subst s
    exact (gammaProduct_heq hd hsel (fun j => Values.vrv (r j))).trans
      ((gammaOrderedSelectedIndex_product P ρ (fun j => Values.vrv (r j))).trans
        (hProduct (fun j => Values.vrv (r j))))
  · intro q p hqp
    obtain ⟨a,ha⟩ := P.surjective p
    have hForm : U.pointForm q = gammaTotalRVCoordinateForm ℓ ω ⟨a.val.2,Set.mem_univ _⟩ := by
      apply gammaSelectedData_heq_form_fibre hd hU (P.toMap a).val
        (gammaTotalRVCoordinateForm ℓ ω ⟨a.val.2,Set.mem_univ _⟩)
        (gammaNativeOrderedEndpoint_form C hBC hv P hP hH ρ hfinH
          (GammaGroundDefSet.univ hc B (rawRVSpace c)) (fun _ => Set.mem_univ _)
          (gammaTotalRVCoordinateForm ℓ ω) a) q
      exact hqp.trans (heq_of_eq (congrArg Subtype.val ha.symm))
    change U.pointForm q = ω ⟨p.val.2 ∘ suffixIndex T.program.rvArity_le,Set.mem_univ _⟩
    rw [hForm]
    apply congrArg ω
    apply Subtype.ext
    funext i
    have hi := P.oldLabels a (ℓ i)
    have he := congrArg (fun z => z.val.2 (suffixIndex P.rvArity_le (ℓ i))) ha
    exact hi.symm.trans (he.trans (congrArg p.val.2 (hLabels i)))

end DiamondIntegral.Section3
