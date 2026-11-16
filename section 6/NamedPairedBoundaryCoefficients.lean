import «section 6».GoodBoundaryCoefficients

/-! A single coefficient named over the original base gives paired
whole-disc images at every point of the actual finite center family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}

theorem scalar_vf_defSet_definable (D : DefSet (rawVFSpace (M := M) 1) S) :
    S.Definable₁ LRV (Subtype.val '' {c : VF M | (fun _ : Fin 1 => c) ∈ D.carrier}) := by
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈
    Subtype.val '' {c : VF M | (fun _ : Fin 1 => c) ∈ D.carrier}}
  have hRaw := D.definable
  change S.Definable LRV ((rawVFSpace (M := M) 1).preimage D.carrier) at hRaw
  suffices hEq : {z : Fin 1 → M | z 0 ∈
      Subtype.val '' {c : VF M | (fun _ : Fin 1 => c) ∈ D.carrier}}=
      (rawVFSpace (M := M) 1).preimage D.carrier by
    rw [hEq]
    exact hRaw
  ext z
  constructor
  · rintro ⟨x,hx,he⟩
    have hCode : vfValues (fun _ : Fin 1 => x)=z := by
      funext i
      fin_cases i
      exact he
    refine ⟨hCode ▸ Set.mem_range_self (fun _ : Fin 1 => x),?_⟩
    have hDecode : (rawVFSpace (M := M) 1).decode
        ⟨z,hCode ▸ Set.mem_range_self (fun _ : Fin 1 => x)⟩=(fun _ : Fin 1 => x) :=
      vfValues_injective ((vfValues_decode _).trans hCode.symm)
    exact hDecode.symm ▸ hx
  · rintro ⟨hz,hzD⟩
    let p := (rawVFSpace (M := M) 1).decode ⟨z,hz⟩
    refine ⟨p 0,?_,?_⟩
    · have hEta : (fun _ : Fin 1 => p 0)=p := by funext i; fin_cases i; rfl
      change (fun _ : Fin 1 => p 0) ∈ D.carrier
      rw [hEta]
      exact hzD
    · exact congrFun (vfValues_decode ⟨z,hz⟩) 0

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem exists_named_paired_boundary_coefficient
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (f : Map A B) (h : ProperCovariantHomeomorphism f)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) (hFinite : E.carrier.Finite) :
    ∃ (c : VF M) (hc0 : c ≠ 0) (hcPos : (1 : GammaInfinity M) < vfValue c),
      S.Definable₁ LRV {c.val} ∧
      uniformBoundaryCoreGood hc f E hEA hRV hD ⟨(fun _ => c),hc0,hcPos⟩ := by
  let D := goodBoundaryCoefficients hc f E hEA hRV hD
  let P : Set (VF M) := {c | (fun _ : Fin 1 => c) ∈ D.carrier}
  have hP := scalar_vf_defSet_definable D
  obtain ⟨η,hη,hAll⟩ := finite_centers_eventual_paired_boundary_codes hc hκ hs hsmall hv f h hRV hD E hEA hFinite
  have hEventual : ∃ ζ : Gamma M,∀ c : VF M,c ≠ 0 → ζ.val < vfValue c → c ∈ P := by
    refine ⟨η,fun c hc0 hcSmall => ?_⟩
    have hPositive : (1 : GammaInfinity M) < vfValue c :=
      (show (1 : GammaInfinity M) ≤ η.val from hη).trans_lt hcSmall
    let c' : positiveBoundaryCoefficients (S := S) hc := ⟨(fun _ => c),hc0,hPositive⟩
    exact (goodBoundaryCoefficients_iff hc f E hEA hRV hD c').mpr (hAll c' hcSmall)
  obtain ⟨c,hc0,hcDef,hcPos,hGood⟩ := exists_named_vf_in_eventual_property h00 hc hv V hV hVS hSV hnt P hP hEventual
  exact ⟨c,hc0,hcPos,hcDef,(goodBoundaryCoefficients_iff hc f E hEA hRV hD
    ⟨(fun _ => c),hc0,hcPos⟩).mp hGood⟩

end DiamondIntegral.Section6
