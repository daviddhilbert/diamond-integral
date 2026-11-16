import «section 6».RegularizationGeometry
import Section4.CodeMaps

/-! The actual regularization map, its proper-covariant homeomorphism
certificate and its everywhere total derivative in fixed RV charts. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def regularizeCodes (z : Fin n ⊕ Fin r → M) : Fin n ⊕ Fin (n+r) → M :=
  Sum.elim (z ∘ Sum.inl) (Fin.append (fun i => iRv (z (.inl i))) (z ∘ Sum.inr))

def regularizeMap (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n (n+r)) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n (n+r)
  let F := regularizeCodes (M := M) (n := n) (r := r)
  have hF : S.DefinableMap LRV F := by
    rintro (i | i)
    · exact Set.DefinableFun.proj LRV
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have hrv : S.DefinableFun LRV (fun z : Fin n ⊕ Fin r → M => iRv (z (.inl i))) :=
          hullRVCode_definable S (.inl i)
        simpa only [F,regularizeCodes,Sum.elim_inr,Fin.append_left] using hrv
      · have hold : S.DefinableFun LRV (fun z : Fin n ⊕ Fin r → M => z (.inr i)) :=
          Set.DefinableFun.proj LRV
        simpa only [F,regularizeCodes,Sum.elim_inr,Fin.append_right,Function.comp_apply] using hold
  have hcode (c : P.domain) : mixedValues (regularize (P.decode c)) = F c.val := by
    have he := mixedValues_decode c
    funext i
    cases i with
    | inl i => exact congrFun he (.inl i)
    | inr i =>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [P,mixedValues,regularize,F,regularizeCodes,rvValues,vfValues,Fin.append_left,Sum.elim_inr,Sum.elim_inl,tupleRV,rv,CanonicalRV.encodedRv] using
          congrArg iRv (congrFun he (.inl i))
      · simpa only [P,mixedValues,regularize,F,regularizeCodes,Fin.append_right,Sum.elim_inr,rvValues,Function.comp_apply] using
          congrFun he (.inr i)
  have hdom (c : P.domain) : F c.val ∈ Q.domain := by
    rw [← hcode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A regularize F hF hdom ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode ⟨F c.val,hdom c⟩).trans (hcode c).symm

def regularization (A : DefSet (rawMixedSpace (M := M) n r) S) := (regularizeMap A).toImage

theorem regularization_apply (A : DefSet (rawMixedSpace (M := M) n r) S) (p : A) :
    (regularization A p).val = regularize p.val := rfl

theorem regularization_carrier (A : DefSet (rawMixedSpace (M := M) n r) S) :
    (regularizeMap A).image.carrier = regularize '' A.carrier := by
  ext q
  exact ⟨fun ⟨p,he⟩ => ⟨p.val,p.property,he⟩,fun ⟨p,hp,he⟩ => ⟨⟨p,hp⟩,he⟩⟩

theorem regularization_bijective (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Function.Bijective (regularization A) := by
  constructor
  · intro p q he
    apply Subtype.ext
    exact regularize_injective (congrArg (fun z : (regularizeMap A).image => z.val) he)
  · rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩

theorem regularization_source_iff (A : DefSet (rawMixedSpace (M := M) n r) S)
    (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource (regularization A) u v ↔
      u = v ∘ Fin.natAdd n ∧ a ∈ vfFibre (regularizeMap A).image.carrier v := by
  constructor
  · rintro ⟨b,p,hp,hfp⟩
    have hVF : b = a := (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)
    subst b
    have hOld : p.val.2 = v ∘ Fin.natAdd n := funext (fun i => by
      simpa only [regularization_apply,regularize,Fin.append_right,Function.comp_apply] using
        congrArg (fun q : Mixed M n (n+r) => q.2 (Fin.natAdd n i)) hfp)
    exact ⟨(congrArg Prod.snd hp).symm.trans hOld,⟨p,hfp⟩⟩
  · rintro ⟨hu,p,hp⟩
    have hVF : p.val.1 = a := congrArg Prod.fst hp
    have hOld : p.val.2 = v ∘ Fin.natAdd n := funext (fun i => by
      simpa only [regularizeMap,Map.ofCodes,Map.toImage,regularize,Fin.append_right,Function.comp_apply] using
        congrArg (fun q : Mixed M n (n+r) => q.2 (Fin.natAdd n i)) hp)
    exact ⟨a,p,Prod.ext hVF (hOld.trans hu.symm),hp⟩

theorem regularization_range_eq_source (A : DefSet (rawMixedSpace (M := M) n r) S)
    (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M) :
    graphFibreRange (regularization A) u v = graphFibreSource (regularization A) u v := by
  ext a
  constructor
  · rintro ⟨b,p,hp,hfp⟩
    have he : b = a := (congrArg Prod.fst hp).symm.trans (congrArg Prod.fst hfp)
    subst b
    exact ⟨a,p,hp,hfp⟩
  · rintro ⟨b,p,hp,hfp⟩
    have he : b = a := (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)
    subst b
    exact ⟨a,p,hp,hfp⟩

theorem regularization_vfChart (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier) (p : A) :
    IsVFChartAt (regularization A) p id := by
  obtain ⟨α,_,hα⟩ := hA.radii p.val.2
  obtain ⟨ε,hε⟩ := (Set.finite_range α).bddAbove
  obtain ⟨γ,hγ⟩ := hVF
  let δ := max ε γ
  refine ⟨δ,fun x hx => ?_⟩
  have hclose : Congruent (fun _ => δ) p.val.1 x := by
    intro i
    change δ.val < Values.vfValueHom (p.val.1 i - x i)
    rw [vfValue_sub_comm]
    exact hx i
  have hxA : (x,p.val.2) ∈ A.carrier :=
    (hα p.val.1 x (hclose.of_larger_radius (fun i =>
      (hε (Set.mem_range_self i)).trans (le_max_left _ _)))).mp p.property
  have hRV : tupleRV M x = tupleRV M p.val.1 := by
    funext i
    exact rv_eq_of_close_at_radius γ (hγ p.val p.property i).2
      ((show γ.val ≤ δ.val from le_max_right _ _).trans_lt (hclose.symm i))
  refine ⟨hxA,?_⟩
  change regularize (x,p.val.2) = (x,(regularize p.val).2)
  exact Prod.ext rfl (congrArg (fun t => Fin.append t p.val.2) hRV)

theorem regularization_unit_derivative (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier) (p : A) :
    HasMixedUnitDerivativeAt (regularization A) p := by
  obtain ⟨L,hL,hdet⟩ := hasUnitJacobianAt_id p.val.1
  exact ⟨L,⟨id,regularization_vfChart A hA hVF p,(hasDerivativeAt_iff_companion _ _ _).mp hL⟩,hdet⟩

theorem regularization_vf_doublyBounded (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hB : ProperInvariant S (regularizeMap A).image.carrier) : VFDoublyBounded A.carrier := by
  obtain ⟨γ,hγ⟩ := hB.rvBounded
  refine ⟨γ,fun p hp i => ?_⟩
  have h := hγ (regularize p) ⟨⟨p,hp⟩,rfl⟩ (Fin.castAdd r i)
  simpa only [regularize,Fin.append_left,tupleRV,vfValue] using h

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem regularization_continuous (A : DefSet (rawMixedSpace (M := M) n r) S) :
    ContinuousOnGraphFibres (regularization A) := by
  intro u v
  have he : Set.EqOn (graphFibreMap (regularization A) u v) id (graphFibreSource (regularization A) u v) := by
    intro a ha
    obtain ⟨p,hp,hfp⟩ := graphFibreMap_graph (regularization A) u v ha
    exact (congrArg Prod.fst hfp).symm.trans (congrArg Prod.fst hp)
  exact continuous_id.continuousOn.congr he

theorem regularization_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier) :
    ProperInvariant S (regularizeMap A).image.carrier := by
  have hEq := regularization_carrier A
  apply (lemma_6_5 h00 hc hκ hs hv _ (regularizeMap A).image.definable
    (hEq.symm ▸ regularized_vfBounded hA.vfBounded)
    (hEq.symm ▸ regularized_rvBounded hVF hA.rvBounded)).mpr
  intro v
  rw [hEq]
  exact regularized_clopen_fibres hv hA hVF v

theorem regularization_properInvariant_iff
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier) :
    ProperInvariant S (regularizeMap A).image.carrier ↔ VFDoublyBounded A.carrier :=
  ⟨regularization_vf_doublyBounded A,regularization_properInvariant h00 hc hκ hs hv A hA⟩

theorem regularization_properCovariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier) :
    ProperCovariant (regularization A) := by
  have hB := regularization_properInvariant h00 hc hκ hs hv A hA hVF
  have hD (u : Fin r → RVInfinity M) (v : Fin (n+r) → RVInfinity M) :
      IsClopen (graphFibreSource (regularization A) u v) := by
    by_cases hu : u = v ∘ Fin.natAdd n
    · have he : graphFibreSource (regularization A) u v = vfFibre (regularizeMap A).image.carrier v :=
        Set.ext (fun a => (regularization_source_iff A u v a).trans (and_iff_right hu))
      exact he.symm ▸ hB.clopen_fibres hv v
    · have he : graphFibreSource (regularization A) u v = ∅ := by
        ext a
        exact ⟨fun ha => False.elim (hu ((regularization_source_iff A u v a).mp ha).1),False.elim⟩
      exact he.symm ▸ isClopen_empty
  apply properCovariant_of_clopen_ranges h00 hc hκ hs hv (regularization A) hA hB
  · exact regularization_continuous A
  · exact fun u v => (hD u v).isOpen
  · intro u v
    rw [regularization_range_eq_source A u v]
    exact hD u v

theorem regularization_properHomeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier) :
    ProperCovariantHomeomorphism (regularization A) :=
  properHomeomorphism_of_properCovariant h00 hc linear hκ hs hv hsmall hΓ
    (regularization A) (regularization_properCovariant h00 hc hκ hs hv A hA hVF)
    (regularization_bijective A) (regularization_continuous A)

end DiamondIntegral.Section6
