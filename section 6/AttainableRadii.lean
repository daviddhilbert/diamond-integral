import «section 6».FiniteProducts
import «section 2».FiniteVFSubset

/-! An original-base definable nonzero VF point can be chosen beyond a
named nonnegative radius. An elementary algebraic-closure model supplies
a finite definable subset; its unordered product removes the algebraic
choices without adding parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def puncturedRadiusBall (δ : Gamma M) : Set (Fin 1 → VF M) :=
  {a | a 0 ≠ 0 ∧ δ.val < vfValue (a 0)}

theorem puncturedRadiusBall_definable {S : Set M} (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) :
    S.Definable LRV (vfValues '' puncturedRadiusBall δ) := by
  have hr : S.DefinableFun LRV (fun z : Fin 1 ⊕ Fin 1 → M => iRv (z (.inl 0))) :=
    rv_scalarCode_definable (Set.DefinableFun.proj LRV)
  have hNZ := (GammaParameters.nonzero_rv_definable S).preimage_map
    (show S.DefinableMap LRV (fun z : Fin 1 ⊕ Fin 1 → M => fun _ : Fin 1 => iRv (z (.inl 0))) from fun _ => hr)
  have hcmp := (rvCode_compare_definable hr
    (show S.DefinableFun LRV (fun z : Fin 1 ⊕ Fin 1 → M => z (.inr 0)) from Set.DefinableFun.proj LRV)).compl
  have h := (((vfRawUniverse_definable S 1).preimage_comp
      (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)).inter hNZ).inter
    ((hδ.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)).inter hcmp)
  convert h.exists_of_finite using 1
  ext z
  constructor
  · rintro ⟨a,⟨ha0,haδ⟩,rfl⟩
    obtain ⟨t,ht,htδ⟩ := GammaParameters.EndpointLogic.codeValue_surjective δ
    have htval : Values.vrv (⟨t,ht.1⟩ : RVInfinity M) = δ.val := by
      rw [← htδ,GammaParameters.codeValue,dite_eq_left ht]
      rfl
    refine ⟨fun _ => t,⟨⟨fun i => (a i).property,?_⟩,?_,?_⟩⟩
    · exact ⟨(rv M (a 0)).property,fun he => ha0 ((CanonicalRV.encodedRv_zero_iff _).mp he)⟩
    · exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr htδ
    · change ¬ iLe (rv M (a 0)).val t
      rw [← Values.vrv_le_iff (rv M (a 0)) (⟨t,ht.1⟩ : RVInfinity M),htval,not_le]
      exact haδ
  · rintro ⟨t,⟨hVF,hNZ⟩,hγ,hcmp⟩
    let a : Fin 1 → VF M := fun i => ⟨z i,hVF i⟩
    let ht : GammaParameters.NonzeroRV (t 0) := ⟨hγ.1,hγ.2.1⟩
    have htδ : GammaParameters.codeValue (t 0) = δ :=
      (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hγ
    have htval : Values.vrv (⟨t 0,ht.1⟩ : RVInfinity M) = δ.val := by
      rw [← htδ,GammaParameters.codeValue,dite_eq_left ht]
      rfl
    refine ⟨a,⟨?_,?_⟩,rfl⟩
    · intro he
      exact hNZ.2 ((CanonicalRV.encodedRv_zero_iff (a 0)).mpr he)
    · change ¬ iLe (rv M (a 0)).val (t 0) at hcmp
      rw [← Values.vrv_le_iff (rv M (a 0)) (⟨t 0,ht.1⟩ : RVInfinity M),htval,not_le] at hcmp
      exact hcmp

theorem puncturedRadiusBall_nonempty (δ : Gamma M) : (puncturedRadiusBall δ).Nonempty := by
  obtain ⟨ε,hε⟩ := exists_gt δ
  obtain ⟨x,hx⟩ := vfValue_surjective ε.val
  have hx0 : x ≠ 0 := by
    intro he
    have hz : vfValue x = Values.infinity := by rw [he,value_zero]
    exact ε.property (hx.symm.trans hz)
  exact ⟨fun _ => x,hx0,by simpa only [hx] using (show δ.val < ε.val from hε)⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G]

theorem exists_named_vf_above_radius (v : Valuation (VF M) G)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    (δ : Gamma M) (hδ0 : (1 : Gamma M) ≤ δ)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) :
    ∃ c : VF M, c ≠ 0 ∧ S.Definable₁ LRV {c.val} ∧ δ.val < vfValue c := by
  classical
  obtain ⟨C,hCA,hCfin,hCne,hCdef⟩ := exists_nonempty_finite_definable_vf_subset v hv hc h00 V S hV hVS hSV hnt
    (puncturedRadiusBall δ) (puncturedRadiusBall_definable δ hδ) (puncturedRadiusBall_nonempty δ)
  let E : Set (VF M) := (fun a : Fin 1 → VF M => a 0) '' C
  have hEfin : E.Finite := hCfin.image _
  let F := hEfin.toFinset
  have hF (x : VF M) : x ∈ F ↔ ∃ a ∈ C, a 0 = x := hEfin.mem_toFinset
  have hFdef : S.Definable₁ LRV (Subtype.val '' (F : Set (VF M))) := by
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' (F : Set (VF M))}
    convert hCdef using 1
    ext z
    constructor
    · rintro ⟨x,hx,hxz⟩
      obtain ⟨a,ha,rfl⟩ := (hF x).mp hx
      exact ⟨a,ha,by funext i; fin_cases i; exact hxz⟩
    · rintro ⟨a,ha,he⟩
      exact ⟨a 0,(hF _).mpr ⟨a,ha,rfl⟩,congrFun he 0⟩
  have hNZ (x : VF M) (hx : x ∈ F) : x ≠ 0 := by
    obtain ⟨a,ha,rfl⟩ := (hF x).mp hx
    exact (hCA ha).1
  have hlarge (x : VF M) (hx : x ∈ F) : δ.val < vfValue x := by
    obtain ⟨a,ha,rfl⟩ := (hF x).mp hx
    exact (hCA ha).2
  let c : VF M := ∏ x ∈ F, x
  refine ⟨c,Finset.prod_ne_zero_iff.mpr hNZ,finiteProduct_definable S F hFdef,?_⟩
  obtain ⟨a,ha⟩ := hCne
  have haF : a 0 ∈ F := (hF _).mpr ⟨a,ha,rfl⟩
  have hp : vfValue c = ∏ x ∈ F, vfValue x := map_prod Values.vfValueHom (fun x => x) F
  rw [hp]
  exact (hlarge (a 0) haF).trans_le (Finset.single_le_prod
    (fun x hx => (show (1 : GammaInfinity M) ≤ δ.val from hδ0).trans (hlarge x hx).le) haF)

end DiamondIntegral.Section6
