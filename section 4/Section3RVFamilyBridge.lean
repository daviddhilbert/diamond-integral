import «section 4».Section3RVRelationBridge
import «section 4».FiniteFamilyBijections
import «section 3».GammaGroundFamilyMaps

/-! Actual finite tagged RV family bijections retain every branch graph
under the raw tuple encoding. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3RVFamilyBridge
open Section3RVCodeBridge FiniteTupleBlocks FiniteFamilyBijections RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem rvValues_join (m n : ℕ) (x : Fin n → CanonicalRV.RVSort M) (y : Fin m → CanonicalRV.RVSort M) :
    rvValues (join m n x y) = join m n (rvValues x) (rvValues y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    exact Fin.cases rfl (fun j => congrFun (ih (Fin.tail x)) j) i

def familyEquiv {n : ℕ} (A : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) n)) :
    A.Carrier ≃ Domain (fun i => rawDomain (A.piece i)) where
  toFun a := ⟨(a.1, rvValues a.2.val), a.2.val, a.2.property, rfl⟩
  invFun a := ⟨a.val.1, (rawEquiv (A.piece a.val.1)).symm ⟨a.val.2, a.property⟩⟩
  left_inv a := by
    change (⟨a.1, (rawEquiv (A.piece a.1)).symm ((rawEquiv (A.piece a.1)) a.2)⟩ : A.Carrier) = a
    rw [Equiv.symm_apply_apply]
    cases a
    rfl
  right_inv a := Subtype.ext (Prod.ext rfl (rawEquiv_symm_value (A.piece a.val.1) ⟨a.val.2, a.property⟩))

def equiv {n m : ℕ} {A : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) n)}
    {D : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) m)} (F : GammaGroundFamilyBijection A D) :
    Domain (fun i => rawDomain (A.piece i)) ≃ Domain (fun j => rawDomain (D.piece j)) :=
  (familyEquiv A).symm.trans (F.equiv.trans (familyEquiv D))

theorem equiv_apply {n m : ℕ} {A : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) n)}
    {D : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) m)} (F : GammaGroundFamilyBijection A D) (a : A.Carrier) :
    equiv F (familyEquiv A a) = familyEquiv D (F.equiv a) := by
  simp only [equiv, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem graph_definable {n m : ℕ} {A : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) n)}
    {D : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) m)} (F : GammaGroundFamilyBijection A D)
    (i : Fin A.tags) (j : Fin D.tags) :
    DefinableOverBase B (fun _ : Fin (m + n) => .rv)
      (graphOn (sourcePiece (equiv F) i j) (pieceMap (equiv F) (fun _ => iRVZero) i)) := by
  have h := (Section3RVRelationBridge.relation_iff (gammaGroundFamilyGraph A D F.equiv i j)).mp (F.definable i j)
  have he : Section3RVRelationBridge.realization (gammaGroundFamilyGraph A D F.equiv i j) =
      graphOn (sourcePiece (equiv F) i j) (pieceMap (equiv F) (fun _ => iRVZero) i) := by
    ext w
    rw [RVRealProducts.graphOn_exists]
    constructor
    · rintro ⟨x, y, ⟨a, b, ha, hb, hab⟩, hw⟩
      have hE := (equiv_apply F ⟨i, a⟩).trans (congrArg (familyEquiv D) hab)
      have ht : (equiv F ⟨(i, rvValues a.val), ⟨a.val, a.property, rfl⟩⟩).val.1 = j := congrArg (fun v => v.val.1) hE
      have hv : pieceMap (equiv F) (fun _ => iRVZero) i (rvValues a.val) = rvValues b.val :=
        (pieceMap_on (equiv F) (fun _ => iRVZero) i _ ⟨a.val, a.property, rfl⟩).trans
          (congrArg (fun v => v.val.2) hE)
      refine ⟨rvValues a.val, ⟨⟨a.val, a.property, rfl⟩, ht⟩, ?_⟩
      rw [hv]
      exact hw.symm.trans ((congrArg rvValues (congrArg₂ (join m n) ha.symm hb.symm)).trans
        (rvValues_join m n a.val b.val))
    · rintro ⟨x, ⟨hx, hj⟩, hw⟩
      let a := (rawEquiv (A.piece i)).symm ⟨x, hx⟩
      have ha : rvValues a.val = x := rawEquiv_symm_value (A.piece i) ⟨x, hx⟩
      have hp : familyEquiv A ⟨i, a⟩ = ⟨(i, x), hx⟩ := Subtype.ext (Prod.ext rfl ha)
      have hE := (congrArg (equiv F) hp).symm.trans (equiv_apply F ⟨i, a⟩)
      obtain ⟨j', b, hF⟩ : ∃ j' b, F.equiv ⟨i, a⟩ = ⟨j', b⟩ := ⟨_, _, rfl⟩
      have ht : j' = j := by
        have htag := congrArg (fun v => v.val.1) hE
        rw [hF] at htag
        exact htag.symm.trans hj
      subst j'
      have hv : pieceMap (equiv F) (fun _ => iRVZero) i x = rvValues b.val := by
        rw [pieceMap_on (equiv F) (fun _ => iRVZero) i x hx]
        exact (congrArg (fun v => v.val.2) hE).trans (congrArg (fun v => rvValues v.2.val) hF)
      refine ⟨a.val, b.val, ⟨a, b, rfl, rfl, hF⟩, ?_⟩
      rw [rvValues_join, ha, ← hv]
      exact hw.symm
  exact (congrArg (fun T => DefinableOverBase B (fun _ : Fin (m + n) => .rv) T) he).mp h

end DiamondIntegral.Section4.Section3RVFamilyBridge
