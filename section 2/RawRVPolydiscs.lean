import «section 2».RVFibrePoints
import «section 2».FinitaryPolydiscPartition

/-! Actual RV polydiscs, including singleton zero factors, and the
RV-row constancy consequence of the full Corollary 2.30 decomposition. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rawRVPolydisc (t : Fin n → RVInfinity M) : Set (Fin n → M) :=
  {x | ∀ j, x j ∈ rvRawFibre (t j)}

theorem rawRVPolydisc_nonempty (t : Fin n → RVInfinity M) : (rawRVPolydisc t).Nonempty := by
  obtain ⟨a,ha⟩ := tupleRV_surjective t
  exact ⟨fun i => (a i).val,fun i => ⟨(a i).property,congrArg Subtype.val (congrFun ha i)⟩⟩

theorem rvRawFibre_mem_zero_iff (t : RVInfinity M) (x : M) (hx : x ∈ rvRawFibre t) :
    x = (0 : VF M).val ↔ t = rvZero M := by
  let a : VF M := ⟨x,hx.1⟩
  have ha : rv M a = t := Subtype.ext hx.2
  rw [← ha,rv_eq_zero_iff]
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

theorem rawRVPolydisc_eq_named_of_nonzero (t : Fin n → RVInfinity M)
    (ht : ∀ i, t i ≠ rvZero M) :
    ∃ (a : Fin n → VF M) (δ : Fin n → Gamma M),
      rawRVPolydisc t = namedPolydisc (fun _ => false) a δ := by
  classical
  choose a δ hD using fun i => rvRawFibre_isOpenDisc (t i) (ht i)
  refine ⟨a,δ,?_⟩
  ext x
  change (∀ i, x i ∈ rvRawFibre (t i)) ↔ ∀ i, x i ∈
    BallImaginaries.underlying (finitePolydiscNames (fun _ => false) a δ i)
  simp only [finitePolydiscNames,Bool.false_eq_true,ite_false]
  exact forall_congr' (fun i => Set.ext_iff.mp (hD i) (x i))

def OpenRVRowsConstant (F : (Fin n → M) → Set M) (V : Set (Fin n → M)) : Prop :=
  ∀ (a : Fin n → VF M) (δ : Fin n → Gamma M), namedPolydisc (fun _ => false) a δ ⊆ V →
    ∀ x ∈ namedPolydisc (fun _ => false) a δ, ∀ y ∈ namedPolydisc (fun _ => false) a δ,
      iRv '' F x = iRv '' F y

def RVPolydiscRowsConstant (F : (Fin n → M) → Set M) (V : Set (Fin n → M)) : Prop :=
  ∀ t : Fin n → RVInfinity M, rawRVPolydisc t ⊆ V →
    ∀ x ∈ rawRVPolydisc t, ∀ y ∈ rawRVPolydisc t, iRv '' F x = iRv '' F y

theorem TaggedPolydiscBranchDecomposition.rows_constant (B : ParameterBase M)
    (a : Fin n → VF M) (δ : Fin n → Gamma M) (F : Set ((Fin n → M) × M))
    (h : TaggedPolydiscBranchDecomposition B a δ F) :
    ∀ x ∈ namedPolydisc (fun _ => false) a δ, ∀ y ∈ namedPolydisc (fun _ => false) a δ,
      iRv '' {v | (x,v) ∈ F} = iRv '' {v | (y,v) ∈ F} := by
  obtain ⟨T,hT,g,hg,hcover⟩ := h
  have hstep (x y : Fin n → M) (hx : x ∈ namedPolydisc (fun _ => false) a δ)
      (hy : y ∈ namedPolydisc (fun _ => false) a δ) (u : M) :
      u ∈ iRv '' {v | (x,v) ∈ F} → u ∈ iRv '' {v | (y,v) ∈ F} := by
    rintro ⟨v,hxv,hvu⟩
    obtain ⟨t,ht,hgtx⟩ := (hcover x hx v).mp hxv
    have htx := ((hg t ht).2.2 x hx v).mpr hgtx
    have hty := ((hg t ht).2.2 y hy (g t y)).mpr rfl
    exact ⟨g t y,hty.1,hty.2.trans (htx.2.symm.trans hvu)⟩
  intro x hx y hy
  ext u
  exact ⟨hstep x y hx hy u,hstep y x hy hx u⟩

end DiamondIntegral.Section2
