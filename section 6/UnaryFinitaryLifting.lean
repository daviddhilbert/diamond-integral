import «section 6».UnaryCenterRepair

/-! Lemma 6.30 in its literal unary RV scope. A finite center family
is constructed over the full VF input; all exceptional input RV discs
are replaced by original-base constant center branches. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

structure UnaryFinitaryLift (R : M → M → Prop)
    (hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))}) where
  center : (Fin 2 → M) → VF M
  definable : S.DefinableFun LRV (fun z => (center z).val)
  prescribed : ∀ a : Fin 1 → VF M, ∀ v, R (iRv (a 0).val) v →
    iRv (center (Fin.snoc (vfValues a) v)).val = v
  differentiable : ∀ p : unaryRVRelationDomain R hR,
    ∃ L : (Fin 1 → VF M) →ₗ[VF M] (Fin 1 → VF M),
      HasMixedVFDerivativeAt (unaryCenterMap center definable (unaryRVRelationDomain R hR)) p L

namespace UnaryFinitaryLift

variable {R : M → M → Prop}
variable {hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))}}

def fibre (T : UnaryFinitaryLift R hR) (a : VF M) : Set (VF M) :=
  {b | ∃ v, R (iRv a.val) v ∧ T.center ![a.val,v] = b}

theorem prescribed_pair (T : UnaryFinitaryLift R hR) (a : VF M) (v : M)
    (hv : R (iRv a.val) v) : iRv (T.center ![a.val,v]).val = v := by
  have he : Fin.snoc (vfValues (fun _ : Fin 1 => a)) v = ![a.val,v] := by
    funext i
    fin_cases i <;> rfl
  simpa only [he] using T.prescribed (fun _ : Fin 1 => a) v hv

theorem fibre_finite (T : UnaryFinitaryLift R hR) (hFin : ∀ u, {v | R u v}.Finite) (a : VF M) :
    (T.fibre a).Finite := by
  apply ((hFin (iRv a.val)).image (fun v => T.center ![a.val,v])).subset
  rintro b ⟨v,hv,he⟩
  exact ⟨v,hv,he⟩

theorem prescribed_fibre (T : UnaryFinitaryLift R hR) (a : VF M) (v : M)
    (hv : R (iRv a.val) v) : ∃! b : VF M, b ∈ T.fibre a ∧ iRv b.val = v := by
  let b := T.center ![a.val,v]
  have hval : iRv b.val = v := T.prescribed_pair a v hv
  refine ⟨b,⟨⟨v,hv,rfl⟩,hval⟩,?_⟩
  rintro c ⟨⟨w,hw,hc⟩,hcv⟩
  have hwval : iRv c.val = w := by
    rw [← hc]
    exact T.prescribed_pair a w hw
  have hwv : w = v := hwval.symm.trans hcv
  rw [hwv] at hc
  exact hc.symm

theorem contracts_to_relation (T : UnaryFinitaryLift R hR) (a : VF M) (v : M) :
    (∃ b ∈ T.fibre a, iRv b.val = v) ↔ R (iRv a.val) v := by
  constructor
  · rintro ⟨b,⟨w,hw,hb⟩,hv⟩
    have hval : iRv b.val = w := by
      rw [← hb]
      exact T.prescribed_pair a w hw
    exact (hval.symm.trans hv) ▸ hw
  · intro hv
    obtain ⟨b,hb,_⟩ := T.prescribed_fibre a v hv
    exact ⟨b,hb⟩

end UnaryFinitaryLift

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Full unary finitary lifting. The source RV sort excludes its
absorbing zero, as in the manuscript's convention for literal RV. -/
theorem lemma_6_30
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (R : M → M → Prop)
    (hR : S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | R (z (.inl 0)) (z (.inr 0))})
    (hFin : ∀ u, {v | R u v}.Finite)
    (hRV : ∀ u v, R u v → iRV v) (hNonzero : ∀ u v, R u v → u ≠ iRVZero) :
    Nonempty (UnaryFinitaryLift R hR) := by
  obtain ⟨f,hf,hval⟩ := exists_unary_relation_center_function hc h00 hs hv V S hV hVS hSV hnt hsmall R hR hFin hRV
  let A := unaryRVRelationDomain R hR
  obtain ⟨E,hEA,hEF,hGood⟩ := exists_unary_differentiability_exception h00 hc hκ hs hsmall hv (unaryCenterMap f hf A)
  let B := unaryRVImage E
  have hB : S.Definable₁ LRV B := unaryRVImage_definable E
  have hBF : B.Finite := unaryRVImage_finite E hEF
  let C := finitaryExceptionalOutputs B R
  have hC : S.Definable₁ LRV C := finitaryExceptionalOutputs_definable B hB R hR
  have hCF : C.Finite := finitaryExceptionalOutputs_finite B hBF R hFin
  obtain ⟨g,hg,hgval⟩ := exists_finite_rv_centers hc h00 hs hv V S hV hVS hSV hnt hsmall C hC hCF
    (fun v ⟨u,_,huv⟩ => hRV u v huv)
  let F := repairedUnaryCenters B f g
  have hF : S.DefinableFun LRV (fun z => (F z).val) := repairedUnaryCenters_definable B hB f hf g hg
  refine ⟨⟨F,hF,?_,?_⟩⟩
  · intro a v hav
    change iRv (repairedUnaryCenters B f g (Fin.snoc (vfValues a) v)).val = v
    rw [repairedUnaryCenters_at]
    by_cases hb : iRv (a 0).val ∈ B
    · simp only [hb,ite_true]
      exact hgval v ⟨iRv (a 0).val,hb,hav⟩
    · simp only [hb,ite_false]
      exact hval a v hav
  · intro p
    have hp0 : p.val.1 0 ≠ 0 := by
      intro he
      exact hNonzero _ _ p.property ((CanonicalRV.encodedRv_zero_iff _).mpr he)
    by_cases hpB : iRv (p.val.1 0).val ∈ B
    · exact ⟨0,repairedUnaryCenterMap_bad_derivative B hB f hf g hg R hR p hp0 hpB⟩
    · have hpE : p.val ∉ E.carrier := by
        intro he
        exact hpB ⟨p.val,he,rfl⟩
      obtain ⟨L,hL⟩ := hGood p hpE
      exact ⟨L,repairedUnaryCenterMap_good_derivative B hB f hf g hg A p hp0 hpB L hL⟩

end DiamondIntegral.Section6
