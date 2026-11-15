import IntegrationSection5.RelativePreparationTrace

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m k : ℕ}
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
theorem relative_prepare_gamma_relation_trace {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (P : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk P.real < κ) (F : VFFieldBase P.real) {n m k : ℕ}
    (r : Point (M := M) (n+1) m → Point (M := M) 0 k → Prop) (hr : GammaGraphDefinable P r) :
    ∃ V : HeadPreparation (PresentedSet.univ (pointSpace (M := M) (n+1) m) P.real),
      SpecialRelativeBoundary V.map 0 none (some false) ∧ (∃ j, Tagged (carrier V.target) 0 j) ∧
        (∀ b c : V.target, SameRV b.val c.val → TailEq b.val c.val → ∀ z,
          r (V.inverseMap b).val z ↔ r (V.inverseMap c).val z) ∧
        ∃ W : UniformRelativeTrace P.real (n+1) (PresentedSet.univ (pointSpace (n+1) m) P.real) V.target,
          ∀ a, W.toMap a = V.map a := by
  have hSupport : GammaPolynomialSupportInput P := gammaPolynomialSupportInput_of_fieldBase P F
  obtain ⟨d,p,hCoeff,hControl⟩ := hSupport r hr
  let A := PresentedSet.univ (pointSpace (M := M) (n+1) m) P.real
  let C := coordinateCanonicalImage A 0
  let W := coordinateCanonicalBijection A 0
  let D := PresentedSet.univ (pointSpace (M := M) d 0) P.real
  let f := mvPolynomialTupleMap C p hCoeff
  let g := Map.comp (flattenKeyMap (PresentedSet.univ (keySpace d 0) P.real)) (Map.comp (keyMap D) f)
  have hA : IsRVPullback (carrier A) := by
    apply (isRVPullback_iff _).mpr
    intro b _ c _
    exact Set.mem_univ _
  have hC := coordinateCanonical_preserves_pullback A 0 hA
  obtain ⟨T,hTb,hTag,hUniform,U,hU⟩ := relative_prepare_realRV_trace hs hsmall h00 C hC
    ⟨Fin.castAdd _ 0,coordinateCanonical_tagged A 0⟩ g
  let Vmap := Map.comp T.map W
  have hVb : SpecialRelativeBoundary Vmap 0 none (some false) :=
    specialRelativeBoundary_comp W T.map 0
      (coordinateCanonical_specialRelativeBoundary A 0 none (by decide)) hTb
  let V : HeadPreparation A := ⟨T.arity,T.target,Vmap,specialRelativeBoundary_forget hVb,T.saturated⟩
  have hComm (b : V.target) : W (V.inverseMap b) = T.inverseMap b := by
    apply T.bijective.1
    rw [T.apply_inverse]
    exact V.apply_inverse b
  have hVF (b : V.target) : vfAt (V.inverseMap b).val = vfAt (T.inverseMap b).val :=
    congrArg (fun q : C => vfAt q.val) (hComm b)
  refine ⟨V,hVb,hTag,?_,UniformRelativeTrace.canonical 0 U,?_⟩
  swap
  · intro a
    exact hU (W a)
  intro b c he ht z
  have hPolys : ∀ i, rv (MvPolynomial.eval (vfAt (V.inverseMap b).val) (p i)) =
      rv (MvPolynomial.eval (vfAt (V.inverseMap c).val) (p i)) := by
    intro i
    rw [hVF b,hVF c]
    have hh := congrFun (congrArg (fun q => q.val.2) (hUniform b c he ht)) (Fin.castAdd 0 i)
    change Fin.append (fun j => rv (MvPolynomial.eval (vfAt (T.inverseMap b).val) (p j))) Fin.elim0 (Fin.castAdd 0 i) =
      Fin.append (fun j => rv (MvPolynomial.eval (vfAt (T.inverseMap c).val) (p j))) Fin.elim0 (Fin.castAdd 0 i) at hh
    simpa only [Fin.append_left] using hh
  exact hControl _ _ (V.inverse_labels b c ((sameRV_iff _ _).mp he).2) hPolys z

end IntegrationInACVF.Section5
