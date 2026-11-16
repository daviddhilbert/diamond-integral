import «section 6».MixedScalarDifferentiability

/-! Rectangular full total derivatives for coefficient tuples. Scalar
component charts assemble on one fixed-label ball, including an empty
output tuple. Finite coefficient families share one small RV label set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r m : ℕ}

def HasMixedVFTupleDerivativeAt {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) m) S)) (p : A)
    (L : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M)) : Prop :=
  ∃ F : (Fin n → VF M) → Fin m → VF M,
    (∃ ρ : Gamma M, ∀ x : Fin n → VF M, x ∈ vfBall p.val.1 ρ →
      ∃ hx : (x,p.val.2) ∈ A.carrier, (f ⟨(x,p.val.2),hx⟩).val = F x) ∧
    HasVFDerivativeAt F p.val.1 L

theorem exists_fixed_label_ball_in_rvLift (U : MeasuredRVObject (M := M) S n) (p : rvLift U.object) :
    ∃ ρ : Gamma M, ∀ x ∈ vfBall p.val.1 ρ, (x,p.val.2) ∈ (rvLift U.object).carrier := by
  have hp0 (i : Fin n) : p.val.1 i ≠ 0 := by
    intro he
    have h := congrArg Subtype.val (congrFun (liftLabelMap_volume U.object p) i)
    change (U.object.value (liftLabelMap U.object p) i).val = (rv M (p.val.1 i)).val at h
    rw [he,rv_zero] at h
    exact U.nonzero (liftLabelMap U.object p) i h
  obtain ⟨ρ,hρ⟩ := nonzero_tuple_rv_ball p.val.1 hp0
  exact ⟨ρ,fun x hx => ⟨liftLabelMap U.object p,rfl,(liftLabelMap_volume U.object p).trans (hρ x hx).symm⟩⟩

theorem tupleDerivative_of_scalar_components {A : DefSet (rawMixedSpace (M := M) n r) S}
    (f : Map A (DefSet.univ (rawVFSpace (M := M) m) S)) (p : A)
    (hOpen : ∃ ρ : Gamma M, ∀ x ∈ vfBall p.val.1 ρ, (x,p.val.2) ∈ A.carrier)
    (hScalar : ∀ j : Fin m, ∃ L,
      HasMixedVFScalarDerivativeAt ((vfTupleSelectMap S (fun _ : Fin 1 => j)).comp f) p L) :
    ∃ L, HasMixedVFTupleDerivativeAt f p L := by
  choose L hL using hScalar
  choose F hChart hDer using hL
  choose ρ hρ using hChart
  obtain ⟨ρ₀,hρ₀⟩ := hOpen
  let R := insert ρ₀ (Finset.univ.image ρ)
  have hR : R.Nonempty := ⟨ρ₀,Finset.mem_insert_self _ _⟩
  let δ := R.max' hR
  have hδ₀ : ρ₀ ≤ δ := Finset.le_max' R ρ₀ (Finset.mem_insert_self _ _)
  have hδ (j : Fin m) : ρ j ≤ δ :=
    Finset.le_max' R (ρ j) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  let D : (Fin n → VF M) →ₗ[VF M] (Fin m → VF M) :=
    LinearMap.pi (fun j => (LinearMap.proj (0 : Fin 1)).comp (L j))
  refine ⟨D,(fun x j => F j x 0),⟨δ,fun x hx => ?_⟩,?_⟩
  · have hxA := hρ₀ x (vfBall_anti hδ₀ hx)
    refine ⟨hxA,funext (fun j => ?_)⟩
    obtain ⟨hxA',hval⟩ := hρ j x (vfBall_anti (hδ j) hx)
    exact congrFun hval 0
  · apply hasVFDerivativeAt_of_components
    intro j
    exact (hDer j).component 0

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_small_rv_labels_for_tuple_differentiability
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : MeasuredRVObject (M := M) S (n+1)) {I : Type} [Finite I] (m : I → ℕ)
    (f : ∀ i, Map (rvLift U.object) (DefSet.univ (rawVFSpace (M := M) (m i)) S)) :
    ∃ D : DefSet (rawRVSpace (M := M) U.object.arity) S, D.carrier ⊆ U.object.domain.carrier ∧
      rvDim D < n+1 ∧ ∀ p : rvLift U.object, p.val.2 ∉ D.carrier →
        ∀ i, ∃ L, HasMixedVFTupleDerivativeAt (f i) p L := by
  let g (j : Σ i, Fin (m i)) := (vfTupleSelectMap S (fun _ : Fin 1 => j.2)).comp (f j.1)
  obtain ⟨D,hD,hDim,hGood⟩ := exists_small_rv_labels_for_scalar_differentiability h00 hc hκ hs hsmall hΓ hv U g
  refine ⟨D,hD,hDim,fun p hp i => ?_⟩
  exact tupleDerivative_of_scalar_components (f i) p (exists_fixed_label_ball_in_rvLift U p)
    (fun j => hGood p hp ⟨i,j⟩)

end DiamondIntegral.Section6
