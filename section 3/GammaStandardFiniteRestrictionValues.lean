import «section 3».GammaStandardRawRestrictionValues
import «section 3».GammaGroundMeasuredRVFinitePartitions

/-! The actual target restrictions of a specified contraction give
finite measured scissors with the whole original Gamma density.
This reuses the proved measured RV finite-partition theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
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
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}

theorem gammaStandard_finite_restriction_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    {ι : Type} [Fintype ι]
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
    (H : ι → SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable B (carrier A)) (hH : ∀ i, GammaSetDefinable B (carrier (H i)))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfinH : ∀ i, ∀ x : Fin (n+1) → VF (M := M), {r | (x,r) ∈ carrier (H i)}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)
    (D : ι → SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 T.arity)
    (P : ∀ i, StandardTargetRestrictionPresentation (G := B) T (H i) (D i))
    (hSub : ∀ i, carrier (D i) ⊆ carrier T.target)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hCover : ∀ q : T.target, ∃ i, q.val ∈ carrier (D i))
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC hA hfinA T hT ω) =
      ∑ i, gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC (hH i) (hfinH i)
        (P i).contraction (P i).gamma ω) := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let U := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC hA hfinA T hT)
  let V (i : ι) := gammaNativeFiniteAt (gammaRawFiniteContraction C.uncountable.le C.saturated hr hBC
    (hH i) (hfinH i) (P i).contraction (P i).gamma)
  let cmp (i : ι) := gammaStandard_raw_restriction_value C hBC hA (hH i) hfinA (hfinH i) T hT (P i) (hSub i) ω
  let R (i : ι) := gammaRestrictAt U (rvObjectDomain (V i).object.obj) (cmp i).choose (V i).domain_graph
  let Ω := gammaNativeTotalRVForm U (suffixIndex T.program.rvArity_le) ω
  let W := gammaNativeMeasuredNormalization U Ω
  let X (i : ι) := W.underlying.domain.inter (Section5.nativeRVGroundDomain (hc := hc) (R i))
  have hDom (i : ι) : (Section5.nativeRVGroundDomain (hc := hc) (R i)).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) (V i)).carrier := by
    rw [Section5.nativeRVGroundDomain_carrier,Section5.nativeRVGroundDomain_carrier]
    rfl
  have hXd : ∀ i j, i ≠ j → Disjoint (X i).carrier (X j).carrier := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro r ⟨_,hri⟩ ⟨_,hrj⟩
    rw [hDom] at hri hrj
    have hi := (gammaNative_raw_contraction_mem (hc := hc) C hBC (hH i) (hfinH i) (P i).contraction (P i).gamma r).mp hri
    have hj := (gammaNative_raw_contraction_mem (hc := hc) C hBC (hH j) (hfinH j) (P j).contraction (P j).gamma r).mp hrj
    exact Set.disjoint_left.mp (hDisj i j hij) hi hj
  have hCov : ∀ r, r ∈ W.underlying.domain.carrier ↔ ∃ i, r ∈ (X i).carrier := by
    intro r
    constructor
    · intro hr
      have hRaw : r ∈ (Section5.nativeRVGroundDomain (hc := hc) U).carrier :=
        (gammaNativeHighLabelInclusion U ⟨r,hr⟩).property
      have hTarget := (gammaNative_raw_contraction_mem (hc := hc) C hBC hA hfinA T hT r).mp hRaw
      obtain ⟨i,hi⟩ := hCover ⟨(Fin.elim0,r),hTarget⟩
      refine ⟨i,hr,?_⟩
      rw [hDom]
      exact (gammaNative_raw_contraction_mem (hc := hc) C hBC (hH i) (hfinH i) (P i).contraction (P i).gamma r).mpr hi
    · rintro ⟨i,hr,_⟩
      exact hr
  have hValue (i : ι) :
      gammaMeasuredPrincipalValue (gammaNativeRawMeasuredContraction C hBC (hH i) (hfinH i)
        (P i).contraction (P i).gamma ω) =
      gammaMeasuredPrincipalValue (W.restrict (X i) (fun _ h => h.1)) := by
    have hComparison := (cmp i).choose_spec
    have e := gammaNativeMeasuredRestrictionHom U (rvObjectDomain (V i).object.obj)
      (cmp i).choose (V i).domain_graph Ω
    exact hComparison.trans (gammaMeasuredPrincipalValue_iso e).symm
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  let f (i : ι) : GammaGroundMeasuredRVPositiveSemiring hc B :=
    gammaGroundMeasuredRVSemiringClass (W.restrict (X i) (fun _ h => h.1))
  have hPartition₀ : gammaGroundMeasuredRVSemiringClass W = ∑ i, f i :=
    gammaGroundMeasuredRVSemiringClass_finite_partition W X hXd hCov
  have hMap : q (∑ i, f i) = ∑ i, q (f i) :=
    _root_.map_sum q.toAddMonoidHom f Finset.univ
  have hPartition : gammaMeasuredPrincipalValue W =
      ∑ i, gammaMeasuredPrincipalValue (W.restrict (X i) (fun _ h => h.1)) :=
    (congrArg q hPartition₀).trans hMap
  change gammaMeasuredPrincipalValue W = _
  exact hPartition.trans (Finset.sum_congr rfl (fun i _ => (hValue i).symm))

end DiamondIntegral.Section3
