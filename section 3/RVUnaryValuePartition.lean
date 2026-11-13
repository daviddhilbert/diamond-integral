import «section 3».ValueFibrePartition
import «section 3».GammaGroundMapRestrictions
import «section 3».GammaGroundSyntaxBridge
import «section 3».GammaTopPresentation
import Section3.AngularPattern
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

abbrev unaryRVValue (t : (rawRVSpace (M := M) 1).Carrier) : Values.GammaTop (M := M) := Values.vrv (t 0)

def unaryRVScalarSet (A : Set (rawRVSpace (M := M) 1).Carrier) : Set M :=
  {x | ∃ t ∈ A, (t 0).val = x}

theorem unaryRVScalarSet_definable (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    GammaParameters.DefinableAtBase ground .rv (unaryRVScalarSet A.carrier) := by
  have he : rvValues '' A.carrier = {z : Fin 1 → M | z 0 ∈ unaryRVScalarSet A.carrier} := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,rfl⟩
    · rintro ⟨t,ht,he⟩
      refine ⟨t,ht,?_⟩
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact he
  change GammaParameters.DefinableOverBase ground (fun _ : Fin 1 => .rv) _
  rw [← he]
  exact A.definable.toRVBase

theorem unaryRVMixedValues_finite (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    (mixedFibreValues unaryRVValue A.carrier).Finite := by
  have hA := (unaryRVScalarSet_definable A).common_names
  obtain ⟨T,hT,_,hpattern⟩ := rv_set_finite_angular_exceptions
    (GammaParameters.commonRealNames ground) _ hA
  let T' : Set (rawRVSpace (M := M) 1).Carrier := {t | (t 0).val ∈ T}
  have hinj : Function.Injective (fun t : (rawRVSpace (M := M) 1).Carrier => (t 0).val) := by
    intro x y he
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact Subtype.ext he
  have hT' : T'.Finite := hT.preimage hinj.injOn
  have hmem (t : (rawRVSpace (M := M) 1).Carrier) :
      (t 0).val ∈ unaryRVScalarSet A.carrier ↔ t ∈ A.carrier := by
    constructor
    · rintro ⟨s,hs,he⟩
      exact hinj he ▸ hs
    · exact fun ht => ⟨t,ht,rfl⟩
  apply mixedFibreValues_finite_of_exceptions unaryRVValue A.carrier T' hT'
  intro x y he hx hy
  exact (hmem x).symm.trans ((hpattern (x 0) (y 0) he hx hy).trans (hmem y))

def unaryRVValueImage (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    GammaGroundDefSet hc ground gammaTopSpace :=
  ⟨unaryRVValue '' A.carrier,A.definable.image (rvGammaTopMap ground.real)⟩

def unaryRVMixedValues (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    GammaGroundDefSet hc ground gammaTopSpace :=
  (unaryRVValueImage A).inter (unaryRVValueImage A.compl)

def unaryRVFullValues (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    GammaGroundDefSet hc ground gammaTopSpace :=
  (unaryRVValueImage A).sdiff (unaryRVValueImage A.compl)

theorem gammaTopInfinity_definable :
    GammaGroundDefinable hc ground gammaTopSpace {Values.infinity (M := M)} := by
  have hd := (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc)).definable.image
    (gammaIncludeTopMap hc ground.real)
  have he : {y | ∃ x : Values.Gamma (M := M), x ∈ (Set.univ : Set (Values.Gamma (M := M))) ∧
      (gammaIncludeTopMap hc ground.real ⟨x,Set.mem_univ _⟩).val = y} =
      ({Values.infinity (M := M)} : Set (Values.GammaTop (M := M)))ᶜ := by
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      exact x.property
    · intro hy
      exact ⟨⟨y,hy⟩,Set.mem_univ _,rfl⟩
  change GammaGroundDefinable hc ground gammaTopSpace
    {y | ∃ x : Values.Gamma (M := M), x ∈ (Set.univ : Set (Values.Gamma (M := M))) ∧
      (gammaIncludeTopMap hc ground.real ⟨x,Set.mem_univ _⟩).val = y} at hd
  rw [he] at hd
  simpa only [compl_compl] using hd.compl

def unaryRVExceptionalValues (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    GammaGroundDefSet hc ground gammaTopSpace :=
  (unaryRVMixedValues A).union ⟨{Values.infinity},gammaTopInfinity_definable⟩

def unaryRVResiduePart (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    GammaGroundDefSet hc ground (rawRVSpace (M := M) 1) :=
  A.inter ⟨unaryRVValue ⁻¹' (unaryRVExceptionalValues A).carrier,
    (unaryRVExceptionalValues A).definable.preimage (rvGammaTopMap ground.real)⟩

def unaryRVCompletePart (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    GammaGroundDefSet hc ground (rawRVSpace (M := M) 1) :=
  ⟨unaryRVValue ⁻¹' ((unaryRVFullValues A).carrier \ {Values.infinity}),
    ((unaryRVFullValues A).definable.inter gammaTopInfinity_definable.compl).preimage (rvGammaTopMap ground.real)⟩

theorem unaryRVExceptionalValues_finite (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    (unaryRVExceptionalValues A).carrier.Finite :=
  (unaryRVMixedValues_finite A).union (Set.finite_singleton _)

theorem unaryRVResiduePart_finite_values (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    ((fun t i => Values.vrv (t i)) '' (unaryRVResiduePart A).carrier).Finite := by
  apply ((unaryRVExceptionalValues_finite A).image (fun y => fun _ : Fin 1 => y)).subset
  rintro _ ⟨t,ht,rfl⟩
  refine ⟨unaryRVValue t,ht.2,?_⟩
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rfl

theorem unaryRVValuePartition (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    (unaryRVResiduePart A).carrier ∪ (unaryRVCompletePart A).carrier = A.carrier :=
  mixed_full_fibre_partition_avoiding unaryRVValue A.carrier {Values.infinity}

theorem unaryRVValuePartition_disjoint (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    Disjoint (unaryRVResiduePart A).carrier (unaryRVCompletePart A).carrier :=
  mixed_full_fibre_disjoint_avoiding unaryRVValue A.carrier {Values.infinity}

theorem unaryRVCompletePart_nonzero (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1))
    (t : unaryRVCompletePart A) : (t.val 0).val ≠ iRVZero := by
  intro hz
  have he := (Values.vrv_eq_infinity_iff (t.val 0)).mpr hz
  exact t.property.2 he
end DiamondIntegral.Section3
