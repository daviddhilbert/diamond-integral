import «section 4».FunctionalApertureCompatibility
import «section 4».GammaOrderLogic
import «section 4».RVPointProductIsomorphisms

/-! The variable annular relation maps into the ordinary homogeneous
measured ideal (P). Its exact factor is the difference of the two base
volume forms times P. Everything is computed in the actual RV rings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4

namespace DiamondIntegral.Section4.VariableApertureMeasuredComparison
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties RVRealProducts FiniteTupleBlocks
open GammaGroupNames RVChartDisjointUnion RVChartRestrictions VariableApertureRayCancellation
open GammaRVLifts GammaRVChartPresentation

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem value_equality_definable (B : Base (M := M)) :
    DefinableOverBase B (fun _ : Fin 2 => .rv)
      {z | Proper z ∧ codeValue (z 0)=codeValue (z 1)} := by
  let A : Empty → Set (Values.Gamma (M := M)) := fun e => nomatch e
  let φ : GammaOrderLogic.Formula Empty 2 :=
    .and (.not (.lt 0 1)) (.not (.lt 1 0))
  have h := GammaOrderLogic.formula_definable_base B A (fun e => nomatch e)
    φ
  change DefinableOverBase B (fun _ : Fin 2 => .rv)
    {z | Proper z ∧ ¬ codeValue (z 0)<codeValue (z 1) ∧ ¬ codeValue (z 1)<codeValue (z 0)} at h
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨hz,not_lt_of_ge he.ge,not_lt_of_ge he.le⟩
  · rintro ⟨hz,h1,h2⟩
    exact ⟨hz,le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)⟩

theorem coefficient_volume_definable (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ u ∈ r.domain, NonzeroRV (u j)) :
    RVVolumeMaps.VolumeDefinable B r.domain (fun u => codeValue (u j)) := by
  let π : Fin 2 → Fin (r.arity+1) := ![0,Fin.succ j]
  have h := (r.domain_definable.preimage_real (fun _ : Fin (r.arity+1) => .rv) Fin.succ).inter
    ((value_equality_definable B).preimage_real (fun _ : Fin (r.arity+1) => .rv) π)
  change DefinableOverBase B (fun _ : Fin (r.arity+1) => .rv)
    {w | Fin.tail w ∈ r.domain ∧ NonzeroRV (w 0) ∧ codeValue (w 0)=codeValue (w j.succ)}
  convert h using 1
  ext w
  change (Fin.tail w ∈ r.domain ∧ NonzeroRV (w 0) ∧ codeValue (w 0)=codeValue (w j.succ)) ↔
    ((Fin.tail w ∈ r.domain ∧ w ∈ sortedUniverse (fun _ => .rv)) ∧
      (Proper (w ∘ π) ∧ codeValue (w 0)=codeValue (w j.succ)) ∧
      w ∈ sortedUniverse (fun _ => .rv))
  constructor
  · rintro ⟨hu,h0,he⟩
    have hs : w ∈ sortedUniverse (fun _ => .rv) :=
      fun i => Fin.cases h0.1 (fun l => r.domain_definable.proper _ hu l) i
    refine ⟨⟨hu,hs⟩,⟨?_,he⟩,hs⟩
    intro i
    fin_cases i
    · exact h0
    · exact hp _ hu
  · rintro ⟨⟨hu,_⟩,⟨hpr,he⟩,_⟩
    exact ⟨hu,hpr 0,he⟩

def shiftedBase (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ u ∈ r.domain, NonzeroRV (u j)) : Chart B k where
  arity := r.arity
  domain := r.domain
  domain_definable := r.domain_definable
  coordinate := r.coordinate
  coordinate_definable := r.coordinate_definable
  coordinate_proper := r.coordinate_proper
  finite_fibres := r.finite_fibres
  volume := fun u => r.volume u*codeValue (u j)
  volume_definable := RVVolumeMaps.multiply_definable B r.domain r.domain_definable
    r.volume (fun u => codeValue (u j)) r.volume_definable (coefficient_volume_definable r j hp)

theorem shiftedBase_weight (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ u ∈ r.domain, NonzeroRV (u j)) (u : Fin r.arity → M) :
    (shiftedBase r j hp).correctedWeight u=r.correctedWeight u*codeValue (u j) := by
  change (r.volume u*codeValue (u j))*(∏ i,codeValue (r.coordinate u i))=
    (r.volume u*(∏ i,codeValue (r.coordinate u i)))*codeValue (u j)
  ac_rfl

theorem ray_weight (B : Base (M := M)) (z : Fin 1 → M) :
    (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B)).correctedWeight z=codeValue (z 0) := by
  change 1*(∏ i : Fin 1,codeValue (z i))=codeValue (z 0)
  simp only [Fin.prod_univ_one,one_mul]

def shiftedRayToDeep (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ u ∈ r.domain, NonzeroRV (u j))
    (hn : ∀ u ∈ r.domain, 1 ≤ codeValue (u j)) :
    Iso (rayProduct (shiftedBase r j hp)) (deepChart r j) where
  equiv := (rayToDeep r j hp hn).equiv
  graph_definable := (rayToDeep r j hp hn).graph_definable
  weight_eq := by
    intro u
    obtain ⟨x,hx,z,hz,he⟩ := (productSet_exists r.domain _ u.val).mp u.property
    change (rayProduct (shiftedBase r j hp)).correctedWeight u.val=
      (rayProduct r).correctedWeight (RVCoefficientShearGraphs.shear j u.val)
    rw [he]
    change (rayProduct (shiftedBase r j hp)).correctedWeight (join 1 r.arity x z)=
      (rayProduct r).correctedWeight (RVCoefficientShearGraphs.shear j (join 1 r.arity x z))
    rw [RVCoefficientShearGraphs.shear_join]
    have hL := product_weight_join (shiftedBase r j hp)
      (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B)) x z
    have hR := product_weight_join r (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B))
      x (RVNamedMultiplication.scale (x j) z)
    change (rayProduct (shiftedBase r j hp)).correctedWeight (join 1 r.arity x z)=_ at hL
    change (rayProduct r).correctedWeight (join 1 r.arity x (RVNamedMultiplication.scale (x j) z))=_ at hR
    rw [hL,hR,ray_weight,ray_weight,shiftedBase_weight]
    change (r.correctedWeight x*codeValue (x j))*codeValue (z (0 : Fin 1))=
      r.correctedWeight x*codeValue (iRVMul (x j) (z (0 : Fin 1)))
    rw [codeValue_mul _ _ (hp x hx) (hz.1 (0 : Fin 1)),mul_assoc]

theorem measured_partition (r : Chart B k) (j : Fin r.arity) :
    RVChartRing.objectClass (annularChart r j)+RVChartRing.objectClass (deepChart r j)=
      RVChartRing.objectClass (rayProduct r) := by
  let a := ofChart (rayProduct r)
  let I := deepDomain r j
  let hI := deepDomain_definable r j
  have hP := RVChartRing.objectClass_iso (partitionIso a I hI)
  have hU := class_disjointUnion (outside a I hI) (inside a I hI) (pieces_disjoint a I hI)
  exact hU.symm.trans hP

theorem point_weight (B : Base (M := M)) (z : Fin 1 → M)
    (hz : z ∈ (RESFibreObjects.point B).domain) :
    (RESFibreObjects.point B).correctedWeight z=1 := by
  have h := RVPointChoices.pointChart_weight B
    (⟨1,(unit_nonzero_code 1).2⟩ : Code (M := M)) (rvNames B).one_mem ⟨z,hz⟩
  exact h.trans (Subtype.ext RVOperations.vrv_one)

def unitProductIso (r : Chart B k) (a : Data B r.arity (1+k))
    (hd : a.domain=r.domain)
    (hw : ∀ u ∈ r.domain,a.toChart.correctedWeight u=r.correctedWeight u) :
    Iso (product r (RESFibreObjects.point B).toChart) a.toChart := by
  refine RVCoordinateMaps.coordinateIso _ _ (headIndex 1 r.arity) ?_ ?_
  · refine ⟨?_,?_,?_⟩
    · intro u hu
      change (u ∘ headIndex 1 r.arity) ∈ a.domain
      rw [hd]
      exact hu.1
    · intro u hu v hv he
      have ht : u ∘ tailIndex 1 r.arity=v ∘ tailIndex 1 r.arity := hu.2.trans hv.2.symm
      exact (join_reconstruct 1 r.arity u).symm.trans
        ((congrArg₂ (join 1 r.arity) he ht).trans (join_reconstruct 1 r.arity v))
    · intro u hu
      let z : Fin 1 → M := ![raw (⟨1,(unit_nonzero_code 1).2⟩ : Code (M := M))]
      refine ⟨join 1 r.arity u z,(productSet_join _ _ _ _).mpr ⟨hd ▸ hu,Set.mem_singleton _⟩,?_⟩
      exact funext (join_head _ _ _ _)
  · intro u hu
    have he := RVPointProductIsomorphisms.product_weight_coordinates r (RESFibreObjects.point B).toChart u
    rw [point_weight B _ hu.2,mul_one] at he
    exact he.trans (hw _ hu.1).symm

theorem relation_formula (P : VariableApertureCompatibility.Presentation B k) :
    RVBoundedMaps.forget B P.relation=
      (RVChartRing.objectClass (shiftedBase P.base.toChart P.apertureIndex P.aperture_nonzero)-
        RVChartRing.objectClass P.base.toChart)*RVMeasuredSpecialClasses.pClass B := by
  have hS := RVChartRing.objectClass_iso
    (unitProductIso P.base.toChart P.source P.source_domain P.source_weight)
  have hE := RVChartRing.objectClass_iso
    (unitProductIso (shiftedBase P.base.toChart P.apertureIndex P.aperture_nonzero)
      P.endpoint P.endpoint_domain (by
        intro u hu
        exact (P.endpoint_weight u hu).trans (shiftedBase_weight _ _ _ _).symm))
  have hD := RVChartRing.objectClass_iso
    (shiftedRayToDeep P.base.toChart P.apertureIndex P.aperture_nonzero P.aperture_nonnegative)
  have hPart := measured_partition P.base.toChart P.apertureIndex
  rw [← hD] at hPart
  simp only [VariableApertureCompatibility.Presentation.relation,map_sub,map_add,
    RVBoundedMaps.forget_class]
  change RVChartRing.objectClass (annularChart P.base.toChart P.apertureIndex)+
    RVChartRing.objectClass P.endpoint.toChart-RVChartRing.objectClass P.source.toChart=_
  rw [← hS,← hE,RVChartRing.objectClass_product,RVChartRing.objectClass_product]
  rw [rayProduct,RVChartRing.objectClass_product,rayProduct,RVChartRing.objectClass_product] at hPart
  unfold RVMeasuredSpecialClasses.pClass
  linear_combination hPart

theorem ideal_maps_into_p (B : Base (M := M)) :
    VariableApertureCompatibility.ideal B ≤
      (Ideal.span {RVMeasuredSpecialClasses.pClass B}).comap (RVBoundedMaps.forget B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨k,P,rfl⟩
  change RVBoundedMaps.forget B P.relation ∈ Ideal.span {RVMeasuredSpecialClasses.pClass B}
  rw [relation_formula]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

theorem functional_ideal_maps_into_p (B : Base (M := M)) :
    FunctionalApertureCompatibility.ideal B ≤
      (Ideal.span {RVMeasuredSpecialClasses.pClass B}).comap (RVBoundedMaps.forget B) :=
  (FunctionalApertureCompatibility.ideal_le_coordinate_ideal B).trans (ideal_maps_into_p B)

end DiamondIntegral.Section4.VariableApertureMeasuredComparison
