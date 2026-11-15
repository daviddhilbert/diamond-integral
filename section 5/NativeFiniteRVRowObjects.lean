import «section 5».NativeRectangleRowValues
import IntegrationSection6.GammaSchemaRowValues

/-! Valid finite label schemata realize actual native RV objects over
the exact parameter base. Their full original label graphs are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
open DiamondIntegral.Section4.FiniteTupleBlocks DiamondIntegral.Section4.RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

def finiteRVSchemaDomain (F : GammaFiniteRVSchema B p a k sp) : GammaDomainFormula B p a sp :=
  ⟨F.domain,F.domain_definable⟩

def finiteRVSchemaLabels (F : GammaFiniteRVSchema B p a k sp) : GammaRelationFormula B p a k sp :=
  ⟨F.volume,F.volume_definable⟩

def finiteRVSchemaRawValue (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (x : Fin a → M) : Fin k → M :=
  if h : ∃! y : Fin k → M, Fin.append (Fin.append z x) y ∈ F.volume
    then h.exists.choose else fun _ => iRVZero

theorem finiteRVSchemaRawValue_mem (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : F.valid z) (x : Fin a → M) (hx : Fin.append z x ∈ F.domain) :
    Fin.append (Fin.append z x) (finiteRVSchemaRawValue F z x) ∈ F.volume := by
  unfold finiteRVSchemaRawValue
  rw [dif_pos (hv.2.1 x hx)]
  exact (hv.2.1 x hx).exists.choose_spec

theorem finiteRVSchemaRawValue_graph (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : F.valid z) (x : Fin a → M) (hx : Fin.append z x ∈ F.domain) (y : Fin k → M) :
    Fin.append (Fin.append z x) y ∈ F.volume ↔ finiteRVSchemaRawValue F z x = y := by
  constructor
  · exact fun hy => (hv.2.1 x hx).unique (finiteRVSchemaRawValue_mem F z hv x hx) hy
  · exact fun hy => hy ▸ finiteRVSchemaRawValue_mem F z hv x hx

theorem finiteRVSchemaRawValue_definable (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : F.valid z) :
    DefinableOverBase ⟨B.real ∪ Set.range z,B.gamma⟩ (fun _ : Fin (k+a) => .rv)
      (graphOn {x | Fin.append z x ∈ F.domain} (finiteRVSchemaRawValue F z)) := by
  convert joinedRelationRow_definable (finiteRVSchemaLabels F) z using 1
  ext w
  change (Fin.append z (w ∘ headIndex k a) ∈ F.domain ∧
    finiteRVSchemaRawValue F z (w ∘ headIndex k a) = w ∘ tailIndex k a) ↔
    Fin.append (Fin.append z (w ∘ headIndex k a)) (w ∘ tailIndex k a) ∈ F.volume
  constructor
  · exact fun h => (finiteRVSchemaRawValue_graph F z hv _ h.1 _).mpr h.2
  · intro h
    have hx := hv.2.2.1 _ _ h
    exact ⟨hx,(finiteRVSchemaRawValue_graph F z hv _ hx _).mp h⟩

theorem finiteRVSchemaRawValue_proper (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : F.valid z) (x : Fin a → M) (hx : Fin.append z x ∈ F.domain) (i : Fin k) :
    iRV (finiteRVSchemaRawValue F z x i) := by
  simpa only [Fin.append_right,sortEval,iRV] using F.volume_definable.proper
    _ (finiteRVSchemaRawValue_mem F z hv x hx) (Fin.natAdd (p+a) i)

def finiteRVSchemaNativeVolume (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : F.valid z) :
    GammaGroundMap (originalRVRowDomain hc (finiteRVSchemaDomain F) z)
      (GammaGroundDefSet.univ hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawRVSpace (M := M) k)) :=
  mapOfRaw {x | Fin.append z x ∈ F.domain}
    (gamma_tuple_parameter_specialize sp (fun _ : Fin a => .rv) z F.domain_definable)
    (finiteRVSchemaRawValue F z) (finiteRVSchemaRawValue_definable F z hv) (finiteRVSchemaRawValue_proper F z hv)

theorem finiteRVSchemaNativeVolume_finite (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : F.valid z) : (finiteRVSchemaNativeVolume (hc := hc) F z hv).FiniteFibres := by
  intro y
  have hf := (hv.2.2.2 (rvValues y.val) (fun j => (y.val j).property)).1
  apply hf.of_injOn (f := fun u : originalRVRowDomain hc (finiteRVSchemaDomain F) z => rvValues u.val)
  · intro u hu
    have hsrc : Fin.append z (rvValues u.val) ∈ F.domain := u.property
    have hg := finiteRVSchemaRawValue_mem F z hv (rvValues u.val) hsrc
    have hy := congrArg (fun v => rvValues v.val) hu
    change finiteRVSchemaRawValue F z (rvValues u.val) = rvValues y.val at hy
    exact hy ▸ hg
  · intro u hu v hv' he
    exact Subtype.ext (rvValues_injective he)

def finiteRVSchemaNativeObject (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : F.valid z)
    (hnz : ∀ x : Fin a → M, ∀ y : Fin k → M,
      Fin.append (Fin.append z x) y ∈ F.volume → ∀ i, y i ≠ iRVZero) :
    GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k where
  arity := a
  domain := originalRVRowDomain hc (finiteRVSchemaDomain F) z
  volume := finiteRVSchemaNativeVolume F z hv
  finite := finiteRVSchemaNativeVolume_finite F z hv
  nonzero := by
    intro u i
    change finiteRVSchemaRawValue F z (rvValues u.val) i ≠ iRVZero
    exact hnz _ _ (finiteRVSchemaRawValue_mem F z hv _ u.property) i

theorem finiteRVSchemaNativeObject_label_graph (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : F.valid z)
    (hnz : ∀ x : Fin a → M, ∀ y : Fin k → M,
      Fin.append (Fin.append z x) y ∈ F.volume → ∀ i, y i ≠ iRVZero)
    (u : (finiteRVSchemaNativeObject (hc := hc) F z hv hnz).domain) (y : Fin k → M) :
    Fin.append (Fin.append z (rvValues u.val)) y ∈ F.volume ↔
      rvValues ((finiteRVSchemaNativeObject F z hv hnz).volume u).val = y :=
  finiteRVSchemaRawValue_graph F z hv _ u.property y

theorem finiteRVSchemaNativeObject_row_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (hv : F.valid z)
    (hnz : ∀ x : Fin a → M, ∀ y : Fin k → M,
      Fin.append (Fin.append z x) y ∈ F.volume → ∀ i, y i ≠ iRVZero) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (finiteRVSchemaDomain F) z =
      nativeRVEvaluation h00 linear hκ hs hc ⟨B.real ∪ Set.range z,B.gamma⟩
        (small_union_range_carrier hκ B.real hr z) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind
        (RVOrdinaryRing.objectClass (Section3RVChartBridge.chart (finiteRVSchemaNativeObject (hc := hc) F z hv hnz))) :=
  (nativeRVSetValue_object h00 linear hκ hs hc _ _ _ _ kind (finiteRVSchemaNativeObject F z hv hnz)).trans
    (nativeGroundRVEvaluation_class h00 linear hκ hs hc _ _ _ _ kind (finiteRVSchemaNativeObject F z hv hnz))

end DiamondIntegral.Section5
