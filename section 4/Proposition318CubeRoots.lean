import «section 4».Proposition318Witness
import «section 3».RVUnitCoordinateTuples
import «section 3».RVResidueFullFibreCoordinates
import «section 3».RVResiduePowerKernels
import «section 3».GammaGroundRVUnitRES
import «section 3».GammaGroundConstants
import «section 3».RVUnitGammaMaps
import «section 3».GammaDivisibleHull

/-! The concrete coefficient of the T001 counterexample: the cube roots of
a ground-definable RV unit `r₀`. If the value of `r₀` is not the cube of a
translation constant (over `ℂ((t))`, `r₀ = rv(t)`: the translation
constants have integer values), then the cube roots form a nonempty finite
RES[0] object of constant value `δ = v(r₀)^{1/3}`, and Proposition 3.18's
kernel is nontrivial. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section4.ResiduePurity
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Proposition318CubeRoots
open GammaEndpointInvariant Proposition318Witness

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- The value of a ground-definable RV unit is Gamma-definable. -/
theorem value_definable (r₀ : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hr : GammaGroundDefinable hc B (rawRVUnitSpace 1) {r₀}) :
    GammaDefinableClosureAtBase B (rvUnitValueHom (r₀ 0)) := by
  let R0 : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) 1) := ⟨{r₀}, hr⟩
  let f : GammaGroundMap R0 (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin 1))) :=
    GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real 1) (fun _ => Set.mem_univ _)
  have himg : (show Set (Fin 1 → Values.Gamma (M := M)) from f.image.carrier) =
      {z | z 0 ∈ ({rvUnitValueHom (r₀ 0)} : Set (Values.Gamma (M := M)))} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      have ha : a.val = r₀ := a.property
      change rvUnitTupleValues a.val 0 = rvUnitValueHom (r₀ 0)
      rw [ha]
      rfl
    · intro hz
      refine ⟨⟨r₀, rfl⟩, ?_⟩
      change rvUnitTupleValues r₀ = z
      funext i
      fin_cases i
      exact hz.symm
  have hdef : GammaOrderLogic.GammaDefinable B {z : Fin 1 → Values.Gamma (M := M) | z 0 ∈ ({rvUnitValueHom (r₀ 0)} : Set _)} := by
    rw [← himg]
    exact (Section3GammaCodeBridge.native_iff _).mp f.image.definable
  exact (GammaOrderLogic.unary_definable_iff B _).mp hdef

theorem value_mem_translation (r₀ : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hr : GammaGroundDefinable hc B (rawRVUnitSpace 1) {r₀}) :
    rvUnitValueHom (r₀ 0) ∈ translationSubgroup hc B :=
  Subgroup.subset_closure ⟨r₀, hr, rfl⟩

/-- The cube roots of `r₀`, as a ground-definable set of RV units. -/
def cubeRoots (r₀ : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hr : GammaGroundDefinable hc B (rawRVUnitSpace 1) {r₀}) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) 1) :=
  (gammaGroundRVUnitRectangularMonomialMap (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1))
    (fun _ _ => (3 : ℤ))).preimage ⟨{r₀}, hr⟩

theorem mem_cubeRoots (r₀ : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hr : GammaGroundDefinable hc B (rawRVUnitSpace 1) {r₀}) (s : Fin 1 → (CanonicalRV.RVSort M)ˣ) :
    s ∈ (cubeRoots r₀ hr).carrier ↔ s 0 ^ 3 = r₀ 0 := by
  constructor
  · rintro ⟨a, ha, hm⟩
    have hm' : (fun _ : Fin 1 => ∏ k : Fin 1, a.val k ^ (3 : ℤ)) = r₀ := hm
    have h0 := congrFun hm' 0
    simp only [Fin.prod_univ_one] at h0
    rw [← ha, ← h0]
    exact (zpow_natCast _ 3).symm
  · intro h
    refine ⟨⟨s, Set.mem_univ _⟩, rfl, ?_⟩
    change (fun _ : Fin 1 => ∏ k : Fin 1, s k ^ (3 : ℤ)) = r₀
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [Fin.prod_univ_one]
    rw [← h]
    exact zpow_natCast _ 3

/-- Every RV unit has a cube root. -/
theorem exists_cube_root (u : (CanonicalRV.RVSort M)ˣ) : ∃ s : (CanonicalRV.RVSort M)ˣ, s ^ 3 = u := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨a, ha⟩ := CanonicalRV.encodedRv_surjective (u : CanonicalRV.RVSort M)
  have ha0 : a ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [← ha]
    exact Subtype.ext (((CanonicalRV.encodedRv_zero_iff a).mpr h).trans RVOperations.zero_val.symm)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (by norm_num : 0 < 3)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact ha0 (by rw [← hb]; ring)
  have hne : RVOperations.rvHom b ≠ 0 := by
    intro h
    exact hb0 ((CanonicalRV.encodedRv_zero_iff b).mp ((congrArg Subtype.val h).trans RVOperations.zero_val))
  refine ⟨Units.mk0 (RVOperations.rvHom b) hne, Units.ext ?_⟩
  change (RVOperations.rvHom b) ^ 3 = (u : CanonicalRV.RVSort M)
  rw [← map_pow, hb]
  exact ha

theorem cube_roots_of_unity_finite :
    {z : (ModelResidue M)ˣ | z ^ 3 = 1}.Finite := by
  apply ((Polynomial.nthRoots 3 (1 : ModelResidue M)).toFinset.finite_toSet).preimage
    (fun x _ y _ h => Units.ext h) |>.subset
  intro z hz
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_nthRoots (by norm_num)]
  have := congrArg Units.val (show z ^ 3 = 1 from hz)
  simpa using this

theorem cubeRoots_finite (h00 : M ⊨ Axioms.ACVF00) (r₀ : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hr : GammaGroundDefinable hc B (rawRVUnitSpace 1) {r₀}) (s₀ : (CanonicalRV.RVSort M)ˣ)
    (hs₀ : s₀ ^ 3 = r₀ 0) : (cubeRoots r₀ hr).carrier.Finite := by
  apply ((cube_roots_of_unity_finite (M := M)).image (fun z => s₀ * residueUnitToRV z) |>.image
    (fun w => (fun _ : Fin 1 => w))).subset
  intro s hs
  have h3 : s 0 ^ 3 = r₀ 0 := (mem_cubeRoots r₀ hr s).mp hs
  have hw : (s 0 * s₀⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, h3, hs₀, mul_inv_cancel]
  have hv : rvUnitValueHom (s 0 * s₀⁻¹) = 1 := by
    have h : rvUnitValueHom (s 0 * s₀⁻¹) ^ 3 = 1 := by rw [← map_pow, hw, map_one]
    exact (pow_eq_one_iff.mp h).resolve_right (by norm_num)
  obtain ⟨z, hz⟩ := exists_residueUnitToRV_of_value_one _ hv
  have hz3 : z ^ 3 = 1 := residueUnitToRV_injective (by rw [map_pow, hz, hw, map_one])
  refine ⟨s 0, ⟨z, hz3, ?_⟩, ?_⟩
  · change s₀ * residueUnitToRV z = s 0
    rw [hz, mul_comm, inv_mul_cancel_right]
  · funext i
    fin_cases i
    rfl

/-- The cube-root coefficient as an RES[0] object. -/
def cubeRootObject (h00 : M ⊨ Axioms.ACVF00) (r₀ : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hr : GammaGroundDefinable hc B (rawRVUnitSpace 1) {r₀}) (s₀ : (CanonicalRV.RVSort M)ˣ)
    (hs₀ : s₀ ^ 3 = r₀ 0) : GammaGroundRESObject hc B 0 := by
  let R := cubeRoots r₀ hr
  let I := (gammaGroundRVUnitToRVMap R).image
  let e := gammaGroundRVUnitPresentationBijection R
  haveI : Finite R := (cubeRoots_finite h00 r₀ hr s₀ hs₀).to_subtype
  haveI : Finite I := Finite.of_surjective _ e.bijective.2
  let c0 : (rawRVSpace (M := M) 0).Carrier := fun i => i.elim0
  have hc0 : GammaGroundDefinable hc B (rawRVSpace (M := M) 0) {c0} := by
    have he : ({c0} : Set (rawRVSpace (M := M) 0).Carrier) =
        (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 0)).carrier :=
      Set.eq_univ_of_forall (fun x => Set.mem_singleton_iff.mpr (funext fun i => i.elim0))
    rw [he]
    exact (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 0)).definable
  let U : GammaGroundRVObject hc B 0 :=
    ⟨1, I, GammaGroundMap.const I c0 hc0, fun _ => Set.toFinite _, fun _ i => i.elim0⟩
  have hres : gammaGroundResProperty U := (Set.toFinite I.carrier).image _
  exact ⟨U, hres⟩

theorem cubeRootObject_domain (h00 : M ⊨ Axioms.ACVF00) (r₀ : Fin 1 → (CanonicalRV.RVSort M)ˣ)
    (hr : GammaGroundDefinable hc B (rawRVUnitSpace 1) {r₀}) (s₀ : (CanonicalRV.RVSort M)ˣ)
    (hs₀ : s₀ ^ 3 = r₀ 0) :
    (cubeRootObject h00 r₀ hr s₀ hs₀).obj.domain = (gammaGroundRVUnitToRVMap (cubeRoots r₀ hr)).image := rfl

/-- **Proposition 3.18, nontriviality from a non-cube value.** If a
ground-definable RV unit `r₀` has a value that is not the cube of any
translation constant, the cube-root coefficient yields an elementary
coefficient pair in the kernel of the unmeasured Ψ with distinct members.
Over `ℂ((t))` with its Gamma names this applies to `r₀ = rv(t)`. -/
theorem proposition_3_18_kernel_nontrivial_of_noncube [CharZero (ModelResidue M)] {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (RY : ∀ (E : Subfield (ModelResidue M)), Cardinal.mk E ≤ Cardinal.aleph0 →
      ∀ [IsAlgClosed E] (a b : Fin 1 → (CanonicalRV.RVSort M)ˣ),
        ReichsteinYoussinInput E (RVOriginalDiagonalWeightGroup B a b))
    (r₀ : Fin 1 → (CanonicalRV.RVSort M)ˣ) (hr : GammaGroundDefinable hc B (rawRVUnitSpace 1) {r₀})
    (hcube : ∀ γ ∈ translationSubgroup hc B, γ ^ 3 ≠ rvUnitValueHom (r₀ 0)) :
    ∃ a b : GammaGroundUnmeasuredPositiveTensor hc B,
      gammaGroundUnmeasuredCoefficientPair a b ∧
        gammaGroundUnmeasuredTensorMap a = gammaGroundUnmeasuredTensorMap b ∧ a ≠ b := by
  obtain ⟨s₀, hs₀⟩ := exists_cube_root (r₀ 0)
  let δ := rvUnitValueHom s₀
  have hδ3 : δ ^ 3 = rvUnitValueHom (r₀ 0) := by rw [← map_pow, hs₀]
  have hδdef : GammaDefinableClosureAtBase B δ :=
    remark_3_14_converse B 3 (by norm_num) δ (hδ3 ▸ value_definable r₀ hr)
  have hvT := value_mem_translation r₀ hr
  have hδT : δ * δ ∉ translationSubgroup hc B := by
    intro h
    apply hcube δ
    · have : δ = rvUnitValueHom (r₀ 0) * (δ * δ)⁻¹ := by rw [← hδ3]; group
      rw [this]
      exact (translationSubgroup hc B).mul_mem hvT ((translationSubgroup hc B).inv_mem h)
    · exact hδ3
  let X := cubeRootObject h00 r₀ hr s₀ hs₀
  let R := cubeRoots r₀ hr
  let e := gammaGroundRVUnitPresentationBijection R
  have hs₀R : (fun _ : Fin 1 => s₀) ∈ R.carrier := (mem_cubeRoots r₀ hr _).mpr hs₀
  have hX : Nonempty X.obj.domain := ⟨e.map ⟨_, hs₀R⟩⟩
  have hav : GammaGroundRESAvailableValueTuple X (fun _ : Fin 1 => δ) := by
    refine ⟨(GammaGroundMap.inclusion (B := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1))
      (fun _ _ => Set.mem_univ _)).comp e.symm.map, ?_⟩
    intro a
    let s := (e.symm.map a).val
    have hsR : s ∈ R.carrier := (e.symm.map a).property
    have h3 : s 0 ^ 3 = r₀ 0 := (mem_cubeRoots r₀ hr s).mp hsR
    funext i
    fin_cases i
    change rvUnitValueHom (s 0) = δ
    have hp : rvUnitValueHom (s 0) ^ 3 = δ ^ 3 := by rw [← map_pow, h3, hδ3]
    exact (pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)) hp
  obtain ⟨hpair, hker, hne⟩ := proposition_3_18_unmeasured_kernel_nontrivial hκ hs h00 hsmall hγsmall RY
    X hX δ hδdef hav hδT
  exact ⟨_, _, hpair, hker, hne⟩

end DiamondIntegral.Section4.Proposition318CubeRoots
