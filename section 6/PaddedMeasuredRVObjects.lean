import «section 6».MeasuredRVHeads
import «section 6».VFCoordinateArithmeticMaps

/-! Padding a nonzero finite-volume measured RV object by constant
unit coordinates retains its old labels, total weight and double bounds.
These pads have value one and do not use absorbing zero coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k m : ℕ}

def rvPadOnesMap (S : Set M) (k m : ℕ) :
    Map (DefSet.univ (rawRVSpace (M := M) k) S) (DefSet.univ (rawRVSpace (M := M) (k+m)) S) := by
  let P := rawRVSpace (M := M) k
  let Q := rawRVSpace (M := M) (k+m)
  let f (x : Fin k → RVInfinity M) : Fin (k+m) → RVInfinity M := productTuple x (fun _ : Fin m => 1)
  let C (z : Fin k → M) : Fin (k+m) → M := productTuple z (fun _ : Fin m => iRVOne)
  have hC : S.DefinableMap LRV C := by
    intro i
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).surjective i
    cases j with
    | inl j =>
      change S.DefinableFun LRV (fun z => productTuple z (fun _ : Fin m => iRVOne) (productLeft k m j))
      simp only [productTuple_left]
      exact Set.DefinableFun.proj LRV
    | inr j =>
      change S.DefinableFun LRV (fun z => productTuple z (fun _ : Fin m => iRVOne) (productRight k m j))
      simp only [productTuple_right]
      exact SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
        (L := LRV) Fn.rvOne Fin.elim0 (fun i => i.elim0))
  have hCode (z : P.domain) : rvValues (f (P.decode z))=C z.val := by
    apply productTuple_ext
    · intro i
      change (productTuple (P.decode z) (fun _ : Fin m => (1 : RVInfinity M)) (productLeft k m i)).val =
        productTuple z.val (fun _ : Fin m => iRVOne) (productLeft k m i)
      rw [productTuple_left,productTuple_left]
      exact congrFun (rvValues_decode z) i
    · intro i
      change (productTuple (P.decode z) (fun _ : Fin m => (1 : RVInfinity M)) (productRight k m i)).val =
        productTuple z.val (fun _ : Fin m => iRVOne) (productRight k m i)
      rw [productTuple_right,productTuple_right]
      exact RVOperations.one_val
  have hDom (z : P.domain) : C z.val ∈ Q.domain := ⟨_,hCode z⟩
  exact Map.ofCodes (DefSet.univ P S) f C hC hDom
    (fun z => rvValues_injective ((rvValues_decode _).trans (hCode z).symm))

theorem rvPadOnesMap_value (S : Set M) (k m : ℕ)
    (x : DefSet.univ (rawRVSpace (M := M) k) S) :
    (rvPadOnesMap S k m x).val=productTuple x.val (fun _ : Fin m => 1) := rfl

theorem rvPadOnesMap_injective (S : Set M) (k m : ℕ) : Function.Injective (rvPadOnesMap (M := M) S k m) := by
  intro x y h
  apply Subtype.ext
  funext i
  have he := congrArg (fun z : DefSet.univ (rawRVSpace (M := M) (k+m)) S => z.val (productLeft k m i)) h
  simpa only [rvPadOnesMap_value,productTuple_left] using he

def measuredRVPadOnes (U : MeasuredRVObject (M := M) S k) (m : ℕ) : MeasuredRVObject (M := M) S (k+m) where
  object := ⟨U.object.arity,U.object.domain,(rvPadOnesMap S k m).comp U.object.volume⟩
  finiteVolume := (Map.finiteFibres_of_injective (rvPadOnesMap_injective S k m)).comp U.finiteVolume
  nonzero u i := by
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).surjective i
    cases j with
    | inl j =>
      change (productTuple (U.object.value u) (fun _ : Fin m => (1 : RVInfinity M)) (productLeft k m j)).val ≠ iRVZero
      rw [productTuple_left]
      exact U.nonzero u j
    | inr j =>
      change (productTuple (U.object.value u) (fun _ : Fin m => (1 : RVInfinity M)) (productRight k m j)).val ≠ iRVZero
      rw [productTuple_right]
      exact (rv_nonzero_code_iff _).mpr one_ne_zero
  form := U.form

theorem measuredRVPadOnes_value (U : MeasuredRVObject (M := M) S k) (m : ℕ) (u : U.object.domain) :
    (measuredRVPadOnes U m).object.value u=productTuple (U.object.value u) (fun _ : Fin m => 1) := rfl

theorem measuredRVPadOnes_volumeGamma (U : MeasuredRVObject (M := M) S k) (m : ℕ) (u : U.object.domain) :
    (measuredRVPadOnes U m).volumeGamma u=U.volumeGamma u := by
  have hOne (h : (1 : RVInfinity M).val ≠ iRVZero) : Values.gammaOf (1 : RVInfinity M) h=(1 : Gamma M) :=
    Subtype.ext RVOperations.vrv_one
  change (∏ i,Values.gammaOf (productTuple (U.object.value u) (fun _ : Fin m => 1) i) _)=_
  rw [← (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).prod_comp,Fintype.prod_sum_type]
  change (∏ i,Values.gammaOf (productTuple (U.object.value u) (fun _ : Fin m => 1) (productLeft k m i)) _) *
    (∏ j,Values.gammaOf (productTuple (U.object.value u) (fun _ : Fin m => 1) (productRight k m j)) _) = _
  simp only [productTuple_left,productTuple_right,hOne,Finset.prod_const_one,mul_one]
  rfl

theorem measuredRVPadOnes_totalWeight (U : MeasuredRVObject (M := M) S k) (m : ℕ) (u : U.object.domain) :
    (measuredRVPadOnes U m).totalWeight u=U.totalWeight u := by
  change gammaMapValue U.form u * (measuredRVPadOnes U m).volumeGamma u=U.totalWeight u
  rw [measuredRVPadOnes_volumeGamma]
  rfl

def measuredRVPadOnesIso {U V : MeasuredRVObject (M := M) S k} (e : MeasuredRVIso U V) (m : ℕ) :
    MeasuredRVIso (measuredRVPadOnes U m) (measuredRVPadOnes V m) where
  iso := rvIsoOfFiniteVolumeNonzero e.iso.hom.map (rvIso_map_bijective e.iso)
    (measuredRVPadOnes U m).finiteVolume (measuredRVPadOnes V m).finiteVolume
    (measuredRVPadOnes U m).nonzero (measuredRVPadOnes V m).nonzero
  balance u := (measuredRVPadOnes_totalWeight U m u).trans
    ((e.balance u).trans (measuredRVPadOnes_totalWeight V m (e.iso.hom.map u)).symm)

theorem measuredRVPadOnes_doublyBounded (U : MeasuredRVObject (M := M) S k) (m : ℕ)
    (hU : U.doublyBounded) : (measuredRVPadOnes U m).doublyBounded := by
  refine ⟨hU.1,?_⟩
  obtain ⟨γ,hγ⟩ := hU.2
  let δ := max γ (1 : Gamma M)
  have hγδ : γ ≤ δ := le_max_left _ _
  have hOneδ : (1 : Gamma M) ≤ δ := le_max_right _ _
  refine ⟨δ,?_⟩
  rintro t ⟨u,rfl⟩ i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).surjective i
  cases j with
  | inl j =>
    change (δ⁻¹).val ≤ Values.vrv (productTuple (U.object.value u) (fun _ : Fin m => 1) (productLeft k m j)) ∧
      Values.vrv (productTuple (U.object.value u) (fun _ : Fin m => 1) (productLeft k m j)) ≤ δ.val
    rw [productTuple_left]
    exact ⟨(show (δ⁻¹).val ≤ (γ⁻¹).val from inv_le_inv' hγδ).trans (hγ _ ⟨u,rfl⟩ j).1,
      (hγ _ ⟨u,rfl⟩ j).2.trans hγδ⟩
  | inr j =>
    change (δ⁻¹).val ≤ Values.vrv (productTuple (U.object.value u) (fun _ : Fin m => 1) (productRight k m j)) ∧
      Values.vrv (productTuple (U.object.value u) (fun _ : Fin m => 1) (productRight k m j)) ≤ δ.val
    rw [productTuple_right,RVOperations.vrv_one]
    exact ⟨show δ⁻¹ ≤ (1 : Gamma M) from by simpa only [inv_one] using inv_le_inv' hOneδ,hOneδ⟩

end DiamondIntegral.Section6
