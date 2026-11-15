import «section 5».NativeFiniteRVRowObjects
import «section 5».OriginalSortedPredicates

/-! Finite RV labels are nonzero by a genuine original-language
first-order predicate. Together with finite-map validity this reconstructs
an actual native RV object over precisely the displayed parameter base. -/
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
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

def finiteRVSchemaLabelsNonzero (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) : Prop :=
  ∀ x : Fin a → M, ∀ y : Fin k → M, Fin.append (Fin.append z x) y ∈ F.volume → ∀ i, y i ≠ iRVZero

theorem finiteRVSchemaLabelsNonzero_original (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaFiniteRVSchema B p a k sp) : OriginalSortedPredicate B sp (finiteRVSchemaLabelsNonzero F) := by
  let st := Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv)) (fun _ : Fin k => SortTag.rv)
  have hcoord (j : Fin k) : OriginalSortedPredicate B st (fun w => NonzeroRV (w (Fin.natAdd (p+a) j))) := by
    let φ := (nativeGammaRelationSyntax hc).proper.relabel (fun _ : Fin 1 => Fin.natAdd (p+a) j)
    have hφ : OriginalSortedPredicate B st (fun w => φ.Realize w) :=
      parameter_free_formula_original_definable hc B st φ
    apply hφ.congr
    intro w hw
    rw [Formula.realize_relabel]
    exact (nativeGammaRelationSyntax hc).proper_realize _
  have hNZ := OriginalSortedPredicate.finite_all hcoord
  have hV := OriginalSortedPredicate.of_definable F.volume_definable
  have hAll := (hV.impl hNZ).all.all
  apply hAll.congr
  intro z hz
  constructor
  · intro h x y hxy i
    have hp := F.volume_definable.proper _ hxy
    have hx : x ∈ sortedUniverse (fun _ : Fin a => SortTag.rv) := fun j => by
      simpa only [Fin.append_left,Fin.append_right] using hp (Fin.castAdd k (Fin.natAdd p j))
    have hy : y ∈ sortedUniverse (fun _ : Fin k => SortTag.rv) := fun j => by
      simpa only [Fin.append_right] using hp (Fin.natAdd (p+a) j)
    simpa only [Fin.append_right] using (h x hx y hy hxy i).2
  · intro h x hx y hy hxy i
    have hp : NonzeroRV (y i) := by
      refine ⟨?_,h x y hxy i⟩
      simpa only [sortEval,iRV] using hy i
    simpa only [Fin.append_right] using hp

def nativeFiniteRVSchemaValid (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) : Prop :=
  F.valid z ∧ finiteRVSchemaLabelsNonzero F z

theorem nativeFiniteRVSchemaValid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaFiniteRVSchema B p a k sp) : DefinableOverBase B sp {z | nativeFiniteRVSchemaValid F z} := by
  have h := F.valid_definable.inter (finiteRVSchemaLabelsNonzero_original hc F)
  convert h using 1
  ext z
  change (F.valid z ∧ finiteRVSchemaLabelsNonzero F z) ↔
    (F.valid z ∧ (z ∈ sortedUniverse sp ∧ finiteRVSchemaLabelsNonzero F z))
  exact ⟨fun h => ⟨h.1,h.1.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩

def nativeFiniteRVSchemaObject (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hv : nativeFiniteRVSchemaValid F z) :
    GammaGroundRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k :=
  finiteRVSchemaNativeObject F z hv.1 hv.2

end DiamondIntegral.Section5
