import «section 6».UnaryCorePlans
import «section 6».UniformFinitePairedCores
import «section 6».FiniteCenterSeparation

/-! Actual finite paired boundary offsets can simultaneously dominate
the two prescribed named floors and separate all original source and
target mixed centres. No preliminary change of VF coordinates or
arbitrary centre-label graft is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}

theorem unaryTaggedDisc_disjoint_of_separated_scalar_discs
    (p q : Mixed M 1 r) (γ δ ρ : Gamma M) (hne : p≠q)
    (hγ : ρ≤γ) (hδ : ρ≤δ)
    (hSep : p.1 0≠q.1 0 → Disjoint (centeredGammaDisc (p.1 0) ρ) (centeredGammaDisc (q.1 0) ρ)) :
    Disjoint (unaryTaggedDisc p γ) (unaryTaggedDisc q δ) := by
  apply Set.disjoint_left.mpr
  rintro a ⟨hap,hp⟩ ⟨haq,hq⟩
  have hScalar : p.1 0≠q.1 0 := by
    intro he
    apply hne
    apply Prod.ext
    · funext i
      fin_cases i
      exact he
    · exact hap.symm.trans haq
  exact Set.disjoint_left.mp (hSep hScalar)
    ((mem_centeredGammaDisc _ _ _).mpr ((show ρ.val≤γ.val from hγ).trans_lt hp))
    ((mem_centeredGammaDisc _ _ _).mpr ((show ρ.val≤δ.val from hδ).trans_lt hq))

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

structure SeparatedUnaryOffsetCores (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) (α β : Gamma M)
    extends UniformFinitePairedCores f E hEA α β where
  sourceSeparated : ∀ p q : E,p≠q → Disjoint
    (unaryTaggedDisc p.val (finiteValue ((sourceOffset p).val 0) (sourceNonzero p)))
    (unaryTaggedDisc q.val (finiteValue ((sourceOffset q).val 0) (sourceNonzero q)))
  targetSeparated : ∀ p q : E,p≠q → Disjoint
    (unaryTaggedDisc (f ⟨p.val,hEA p.property⟩).val (finiteValue ((targetOffset p).val 0) (targetNonzero p)))
    (unaryTaggedDisc (f ⟨q.val,hEA q.property⟩).val (finiteValue ((targetOffset q).val 0) (targetNonzero q)))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_separated_unary_offset_cores
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x≠0 ∧ Valued.v x.val≠1)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) (hE : E.carrier.Finite)
    (α β : Gamma M)
    (hα : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    Nonempty (SeparatedUnaryOffsetCores f E hEA α β) := by
  letI : Fintype E := hE.fintype
  let aMap := mixedVFHeadMap E
  let bMap := (mixedVFHeadMap B).comp (f.restrict hEA)
  let H := scalarFocusImage aMap ∪ scalarFocusImage bMap
  have hH : S.Definable₁ LRV (Subtype.val '' H) := by
    rw [Set.image_union]
    exact (scalarFocusImage_definable aMap).union (scalarFocusImage_definable bMap)
  have hHFin : H.Finite := (Set.finite_range _).union (Set.finite_range _)
  obtain ⟨t,ht0,htNamed,htPos,hSeparate⟩ := exists_named_separating_radius h00 hc hv
    V hV hVS hSV hnt H hH hHFin
  let ρ := finiteValue t ht0
  have hρ := finiteValue_named t ht0 htNamed (S := S)
  obtain ⟨D⟩ := exists_uniform_finite_paired_cores h00 hc hκ hs hsmall hv V hV hVS hSV hnt
    f hf hRV hD E hEA hE (max α ρ) (max β ρ)
    (gamma_max_named α ρ hα hρ) (gamma_max_named β ρ hβ hρ)
  have hSource (p : E) : ρ≤finiteValue ((D.sourceOffset p).val 0) (D.sourceNonzero p) :=
    (le_max_right _ _).trans (show max α ρ<finiteValue ((D.sourceOffset p).val 0) (D.sourceNonzero p) from D.sourceFloor p).le
  have hTarget (p : E) : ρ≤finiteValue ((D.targetOffset p).val 0) (D.targetNonzero p) :=
    (le_max_right _ _).trans (show max β ρ<finiteValue ((D.targetOffset p).val 0) (D.targetNonzero p) from D.targetFloor p).le
  refine ⟨{
    sourceOffset := D.sourceOffset
    targetOffset := D.targetOffset
    sourceNonzero := D.sourceNonzero
    targetNonzero := D.targetNonzero
    sourceFloor := fun p => (show α.val≤(max α ρ).val from le_max_left _ _).trans_lt (D.sourceFloor p)
    targetFloor := fun p => (show β.val≤(max β ρ).val from le_max_left _ _).trans_lt (D.targetFloor p)
    sourceDisc := D.sourceDisc
    targetDisc := D.targetDisc
    image := D.image
    sourceSeparated := ?_
    targetSeparated := ?_ }⟩
  · intro p q hpq
    apply unaryTaggedDisc_disjoint_of_separated_scalar_discs p.val q.val _ _ ρ
      (fun he => hpq (Subtype.ext he)) (hSource p) (hSource q)
    exact hSeparate _ (Or.inl ⟨p,rfl⟩) _ (Or.inl ⟨q,rfl⟩)
  · intro p q hpq
    have hne : (f ⟨p.val,hEA p.property⟩).val≠(f ⟨q.val,hEA q.property⟩).val := by
      intro he
      have h := hf.bijective.injective (Subtype.ext he)
      have hValue := congrArg (fun a : A => a.val) h
      exact hpq (Subtype.ext hValue)
    apply unaryTaggedDisc_disjoint_of_separated_scalar_discs _ _ _ _ ρ hne (hTarget p) (hTarget q)
    exact hSeparate _ (Or.inr ⟨p,rfl⟩) _ (Or.inr ⟨q,rfl⟩)

end DiamondIntegral.Section6
