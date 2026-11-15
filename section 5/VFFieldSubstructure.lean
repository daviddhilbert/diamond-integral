import «section 5».VFFieldRVImage
import Section3.RVOperations

/-! An actual VF subfield with precisely its RV images forms a genuine
substructure of the original language, with the same VF field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open CanonicalRV ValuedModelMap
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (F : Subfield (VFType (M := M)))

def vfFieldCarrier : Set M := vfFieldNames F ∪ Subtype.val '' vfFieldRVImage F

theorem vfFieldCarrier_vf (a : VFType (M := M)) : a.val ∈ vfFieldCarrier F ↔ a ∈ F := by
  constructor
  · rintro (⟨b,hb,he⟩ | ⟨r,hr,he⟩)
    · exact Subtype.ext he ▸ hb
    · exact (TypedModelMap.not_rv_of_vf a.property (he ▸ r.property)).elim
  · intro ha
    exact Or.inl ⟨a,ha,rfl⟩

theorem vfFieldCarrier_rv (a : RVSort M) : a.val ∈ vfFieldCarrier F ↔ a ∈ vfFieldRVImage F := by
  constructor
  · rintro (⟨b,hb,he⟩ | ⟨r,hr,he⟩)
    · exact (TypedModelMap.not_vf_of_rv a.property (he ▸ b.property)).elim
    · exact Subtype.ext he ▸ hr
  · exact fun ha => Or.inr ⟨a,ha,rfl⟩

theorem vfFieldCarrier_zero (σ : SortTag) : CanonicalStructure.sortZero (M := M) σ ∈ vfFieldCarrier F := by
  cases σ
  · exact (vfFieldCarrier_vf F 0).mpr F.zero_mem
  · exact (vfFieldCarrier_rv F zeroRV).mpr (vfFieldRVImage_zero F)

def vfFieldSubstructure : LRV.Substructure M where
  carrier := vfFieldCarrier F
  fun_mem := by
    intro n f xs hxs
    by_cases hsort : ∀ i,sortEval (Fn.argSort f i) (xs i)
    · have vf (i : Fin n) (h : iVF (xs i)) : (⟨xs i,h⟩ : VFType (M := M)) ∈ F :=
        (vfFieldCarrier_vf F _).mp (hxs i)
      have rv (i : Fin n) (h : iRV (xs i)) : (⟨xs i,h⟩ : RVSort M) ∈ vfFieldRVImage F :=
        (vfFieldCarrier_rv F _).mp (hxs i)
      cases f with
      | vfZero =>
        have he : xs = Fin.elim0 := Subsingleton.elim _ _
        subst xs
        exact (vfFieldCarrier_vf F 0).mpr F.zero_mem
      | vfOne =>
        have he : xs = Fin.elim0 := Subsingleton.elim _ _
        subst xs
        exact (vfFieldCarrier_vf F 1).mpr F.one_mem
      | vfAdd =>
        let a : VFType (M := M) := ⟨xs 0,hsort 0⟩
        let b : VFType (M := M) := ⟨xs 1,hsort 1⟩
        have he : Structure.funMap (L := LRV) Fn.vfAdd xs = (a+b).val := by
          change Structure.funMap (L := LRV) Fn.vfAdd xs = Structure.funMap (L := LRV) Fn.vfAdd ![xs 0,xs 1]
          congr 1; funext i; fin_cases i <;> rfl
        exact he ▸ (vfFieldCarrier_vf F (a+b)).mpr (F.add_mem (vf 0 (hsort 0)) (vf 1 (hsort 1)))
      | vfMul =>
        let a : VFType (M := M) := ⟨xs 0,hsort 0⟩
        let b : VFType (M := M) := ⟨xs 1,hsort 1⟩
        have he : Structure.funMap (L := LRV) Fn.vfMul xs = (a*b).val := by
          change Structure.funMap (L := LRV) Fn.vfMul xs = Structure.funMap (L := LRV) Fn.vfMul ![xs 0,xs 1]
          congr 1; funext i; fin_cases i <;> rfl
        exact he ▸ (vfFieldCarrier_vf F (a*b)).mpr (F.mul_mem (vf 0 (hsort 0)) (vf 1 (hsort 1)))
      | vfNeg =>
        let a : VFType (M := M) := ⟨xs 0,hsort 0⟩
        have he : Structure.funMap (L := LRV) Fn.vfNeg xs = (-a).val := by
          change Structure.funMap (L := LRV) Fn.vfNeg xs = Structure.funMap (L := LRV) Fn.vfNeg ![xs 0]
          congr 1; funext i; fin_cases i; rfl
        exact he ▸ (vfFieldCarrier_vf F (-a)).mpr (F.neg_mem (vf 0 (hsort 0)))
      | rvZero =>
        have he : xs = Fin.elim0 := Subsingleton.elim _ _
        subst xs
        exact (vfFieldCarrier_rv F zeroRV).mpr (vfFieldRVImage_zero F)
      | rvOne =>
        have he : xs = Fin.elim0 := Subsingleton.elim _ _
        subst xs
        exact (vfFieldCarrier_rv F oneRV).mpr (vfFieldRVImage_one F)
      | rvMap =>
        let a : VFType (M := M) := ⟨xs 0,hsort 0⟩
        have he : Structure.funMap (L := LRV) Fn.rvMap xs = (encodedRv a).val := by
          change Structure.funMap (L := LRV) Fn.rvMap xs = Structure.funMap (L := LRV) Fn.rvMap ![xs 0]
          congr 1; funext i; fin_cases i; rfl
        exact he ▸ (vfFieldCarrier_rv F (encodedRv a)).mpr ⟨a,vf 0 (hsort 0),rfl⟩
      | rvMul =>
        let a : RVSort M := ⟨xs 0,hsort 0⟩
        let b : RVSort M := ⟨xs 1,hsort 1⟩
        have he : Structure.funMap (L := LRV) Fn.rvMul xs = (mulRV a b).val := by
          change Structure.funMap (L := LRV) Fn.rvMul xs = Structure.funMap (L := LRV) Fn.rvMul ![xs 0,xs 1]
          congr 1; funext i; fin_cases i <;> rfl
        exact he ▸ (vfFieldCarrier_rv F (mulRV a b)).mpr (vfFieldRVImage_mul F (rv 0 (hsort 0)) (rv 1 (hsort 1)))
      | rvInv =>
        let a : RVSort M := ⟨xs 0,hsort 0⟩
        obtain ⟨x,hx,hxa⟩ := rv 0 (hsort 0)
        have he : Structure.funMap (L := LRV) Fn.rvInv xs = ((encodedRv x)⁻¹).val := by
          rw [RVOperations.inv_val,hxa]
          change Structure.funMap (L := LRV) Fn.rvInv xs = Structure.funMap (L := LRV) Fn.rvInv ![xs 0]
          congr 1; funext i; fin_cases i; rfl
        have hi : (encodedRv x)⁻¹ = encodedRv (x⁻¹) := (map_inv₀ RVOperations.rvHom x).symm
        rw [he,hi]
        exact (vfFieldCarrier_rv F (encodedRv (x⁻¹))).mpr ⟨x⁻¹,F.inv_mem hx,rfl⟩
      | kAdd =>
        let a : RVSort M := ⟨xs 0,hsort 0⟩
        let b : RVSort M := ⟨xs 1,hsort 1⟩
        have he : Structure.funMap (L := LRV) Fn.kAdd xs = (addK a b).val := by
          change Structure.funMap (L := LRV) Fn.kAdd xs = Structure.funMap (L := LRV) Fn.kAdd ![xs 0,xs 1]
          congr 1; funext i; fin_cases i <;> rfl
        exact he ▸ (vfFieldCarrier_rv F (addK a b)).mpr (vfFieldRVImage_add F (rv 0 (hsort 0)) (rv 1 (hsort 1)))
      | kNeg =>
        let a : RVSort M := ⟨xs 0,hsort 0⟩
        have he : Structure.funMap (L := LRV) Fn.kNeg xs = (negK a).val := by
          change Structure.funMap (L := LRV) Fn.kNeg xs = Structure.funMap (L := LRV) Fn.kNeg ![xs 0]
          congr 1; funext i; fin_cases i; rfl
        exact he ▸ (vfFieldCarrier_rv F (negK a)).mpr (vfFieldRVImage_neg F (rv 0 (hsort 0)))
    · rw [hc.1 f xs hsort]
      exact vfFieldCarrier_zero F _

def vfFieldSubstructureBase : Section2.VFGeneratedFieldBase (vfFieldSubstructure hc F) where
  field := F
  mem_iff := fun a => (vfFieldCarrier_vf F a).symm
  rv_lift := by
    intro t ht htr
    obtain ⟨x,hx,hxt⟩ := (vfFieldCarrier_rv F ⟨t,htr⟩).mp ht
    exact ⟨⟨x,hx⟩,congrArg Subtype.val hxt⟩

end DiamondIntegral.Section5
