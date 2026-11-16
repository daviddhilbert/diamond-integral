import «section 6».NamedPositiveChoice

/-! A common finite aperture coefficient for a finite definable family
of nonzero unary foci. Its complete code formula is over the original
base; the temporary Gamma representative is existentially quantified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def ApertureCoefficients (C : Set (VF M)) (δ : Gamma M) : Set (VF M) :=
  {c | c ≠ 0 ∧ (1 : GammaInfinity M) ≤ vfValue c ∧ ∀ a ∈ C, δ.val < vfValue (c*a)}

theorem apertureCoefficients_definable (C : Set (VF M))
    (hC : S.Definable₁ LRV (Subtype.val '' C)) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) :
    S.Definable₁ LRV (Subtype.val '' ApertureCoefficients C δ) := by
  let I := Fin 1 ⊕ Fin 1
  have hr : S.DefinableFun LRV (fun z : I → M => iRv (z (.inl 0))) :=
    rv_scalarCode_definable (Set.DefinableFun.proj LRV)
  have hNZ := (GammaParameters.nonzero_rv_definable S).preimage_map
    (show S.DefinableMap LRV (fun z : I → M => fun _ : Fin 1 => iRv (z (.inl 0))) from fun _ => hr)
  have hpos := rvCode_compare_definable (branchTag_definable S false) hr
  have hprod : S.DefinableFun LRV
      (fun z : I ⊕ Fin 1 → M => iRv (iVFMul (z (.inl (.inl 0))) (z (.inr 0)))) :=
    rv_scalarCode_definable (scalarMulCode_definable
      (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV))
  have hcmp := rvCode_compare_definable hprod
    (show S.DefinableFun LRV (fun z : I ⊕ Fin 1 → M => z (.inl (.inr 0))) from Set.DefinableFun.proj LRV)
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' C} at hC
  have hbad := (hC.preimage_comp (Sum.inr : Fin 1 → I ⊕ Fin 1)).inter hcmp
  have hAll := hbad.exists_of_finite.compl
  have h := (((((vfRawUniverse_definable S 1).preimage_comp
    (Sum.inl : Fin 1 → I)).inter hNZ).inter hpos).inter
    (hδ.preimage_comp (Sum.inr : Fin 1 → I))).inter hAll
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' ApertureCoefficients C δ}
  convert h.exists_of_finite using 1
  ext z
  constructor
  · rintro ⟨c,⟨hc0,hcpos,hcf⟩,hcz⟩
    obtain ⟨t,ht,htδ⟩ := GammaParameters.EndpointLogic.codeValue_surjective δ
    have htval : Values.vrv (⟨t,ht.1⟩ : RVInfinity M) = δ.val := by
      rw [← htδ,GammaParameters.codeValue,dite_eq_left ht]
      rfl
    refine ⟨fun _ => t,⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩⟩
    · intro i
      fin_cases i
      change iVF (z 0)
      rw [← hcz]
      exact c.property
    · change GammaParameters.NonzeroRV (iRv (z 0))
      rw [← hcz]
      exact ⟨(rv M c).property,fun he => hc0 ((CanonicalRV.encodedRv_zero_iff c).mp he)⟩
    · change iLe (rv M (1 : VF M)).val (iRv (z 0))
      rw [← hcz]
      change iLe (rv M (1 : VF M)).val (rv M c).val
      apply (Values.vrv_le_iff (rv M 1) (rv M c)).mp
      change vfValue (1 : VF M) ≤ vfValue c
      rw [show vfValue (1 : VF M) = 1 from Values.vf_value_one]
      exact hcpos
    · exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr htδ
    · rintro ⟨w,⟨a,ha,haw⟩,hcmp⟩
      have hew : w 0 = a.val := haw.symm
      change iLe (iRv (iVFMul (z 0) (w 0))) t at hcmp
      rw [← hcz,hew] at hcmp
      change iLe (rv M (@HMul.hMul (VF M) (VF M) (VF M) inferInstance c a)).val t at hcmp
      have hle := (Values.vrv_le_iff (rv M (@HMul.hMul (VF M) (VF M) (VF M) inferInstance c a)) (⟨t,ht.1⟩ : RVInfinity M)).mpr hcmp
      rw [htval] at hle
      exact (not_le_of_gt (hcf a ha)) hle
  · rintro ⟨t,⟨⟨⟨⟨hVF,hNZ⟩,hpos⟩,hγ⟩,hAll⟩⟩
    let c : VF M := ⟨z 0,hVF 0⟩
    let ht : GammaParameters.NonzeroRV (t 0) := ⟨hγ.1,hγ.2.1⟩
    have htδ : GammaParameters.codeValue (t 0) = δ :=
      (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hγ
    have htval : Values.vrv (⟨t 0,ht.1⟩ : RVInfinity M) = δ.val := by
      rw [← htδ,GammaParameters.codeValue,dite_eq_left ht]
      rfl
    refine ⟨c,⟨?_,?_,?_⟩,rfl⟩
    · intro he
      exact hNZ.2 ((CanonicalRV.encodedRv_zero_iff c).mpr he)
    · change iLe (rv M (1 : VF M)).val (rv M c).val at hpos
      have hp := (Values.vrv_le_iff (rv M 1) (rv M c)).mpr hpos
      change vfValue (1 : VF M) ≤ vfValue c at hp
      rw [show vfValue (1 : VF M) = 1 from Values.vf_value_one] at hp
      exact hp
    · intro a ha
      by_contra! hle
      apply hAll
      refine ⟨fun _ : Fin 1 => a.val,⟨a,ha,rfl⟩,?_⟩
      change iLe (rv M (@HMul.hMul (VF M) (VF M) (VF M) inferInstance c a)).val (t 0)
      apply (Values.vrv_le_iff (rv M (@HMul.hMul (VF M) (VF M) (VF M) inferInstance c a)) (⟨t 0,ht.1⟩ : RVInfinity M)).mp
      rwa [htval]

theorem apertureCoefficients_nonempty (C : Set (VF M)) (hC : C.Finite)
    (hC0 : ∀ a ∈ C, a ≠ 0) (δ : Gamma M) : (ApertureCoefficients C δ).Nonempty := by
  classical
  letI : Fintype C := hC.fintype
  let R : Set (Gamma M) := (fun a : C => δ / finiteValue a.val (hC0 a.val a.property)) '' Set.univ
  have hR : R.Finite := Set.finite_univ.image _
  obtain ⟨η,hη⟩ := hR.bddAbove
  obtain ⟨γ,hγ⟩ := exists_gt (max 1 η)
  obtain ⟨c,hcval⟩ := vfValue_surjective γ.val
  have hc0 : c ≠ 0 := by
    intro he
    exact γ.property (hcval.symm.trans (by rw [he,value_zero]))
  refine ⟨c,hc0,?_,?_⟩
  · exact (show (1 : GammaInfinity M) ≤ γ.val from (le_max_left 1 η).trans hγ.le).trans_eq hcval.symm
  · intro a ha
    have hlt : δ / finiteValue a (hC0 a ha) < γ :=
      (hη ⟨⟨a,ha⟩,Set.mem_univ _,rfl⟩).trans_lt ((le_max_right 1 η).trans_lt hγ)
    have he : δ.val < γ.val * vfValue a := by
      exact show δ < γ * finiteValue a (hC0 a ha) from (div_lt_iff_lt_mul).mp hlt
    change δ.val < Values.vfValueHom (c*a)
    rw [map_mul]
    change δ.val < vfValue c * vfValue a
    rwa [hcval]

variable {G : Type} [LinearOrderedCommGroupWithZero G]

theorem exists_named_aperture_coefficient (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    (C : Set (VF M)) (hC : S.Definable₁ LRV (Subtype.val '' C)) (hCf : C.Finite)
    (hC0 : ∀ a ∈ C, a ≠ 0) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) :
    ∃ c : VF M, c ≠ 0 ∧ (1 : GammaInfinity M) ≤ vfValue c ∧ S.Definable₁ LRV {c.val} ∧
      ∀ a ∈ C, δ.val < vfValue (c*a) := by
  obtain ⟨c,hcP,hcdef⟩ := exists_named_positive_choice v hv hc h00 V S hV hVS hSV hnt
    (ApertureCoefficients C δ) (apertureCoefficients_definable C hC δ hδ)
    (apertureCoefficients_nonempty C hCf hC0 δ) (fun _ h => ⟨h.1,h.2.1⟩) (by
      intro a ha b hb hab
      refine ⟨hb,ha.2.1.trans hab,fun z hz => ?_⟩
      have hm := mul_le_mul' hab (le_refl (vfValue z))
      change δ.val < Values.vfValueHom (b*z)
      rw [map_mul]
      have hstart := ha.2.2 z hz
      change δ.val < Values.vfValueHom (a*z) at hstart
      rw [map_mul] at hstart
      exact hstart.trans_le hm)
  exact ⟨c,hcP.1,hcP.2.1,hcdef,hcP.2.2⟩

end DiamondIntegral.Section6
