import «section 5».RESRelationTotalValues

/-! Every full original bijective RV row graph realizes an actual
bijection over precisely the displayed parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 DiamondIntegral.Section4.FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b : ℕ} {sp : Fin p → SortTag}

def originalRVRowBijection
    (D : GammaDomainFormula B p a sp) (E : GammaDomainFormula B p b sp)
    (H : GammaRelationFormula B p a b sp) (z : Fin p → M)
    (hv : bijectiveMapRowValid sp (fun _ : Fin b => .rv) D.val E.val H.val z) :
    GammaGroundBijection (originalRVRowDomain hc D z) (originalRVRowDomain hc E z) := by
  let F : RESSetSchema B p a sp := ⟨D,0⟩
  let G : RESSetSchema B p b sp := ⟨E,0⟩
  let e : F.rowDomain z ≃ G.rowDomain z := hv.equiv
    (fun y hy j => by simpa only [Fin.append_right] using E.property.proper _ hy (Fin.natAdd p j))
  have he (x : Fin a → M) (y : Fin b → M) :
      Fin.append (Fin.append z x) y ∈ H.val ↔ ∃ u : F.rowDomain z, u.val = x ∧ (e u).val = y :=
    hv.equiv_graph _ x y
  have hg : DefinableOverBase ⟨B.real ∪ Set.range z,B.gamma⟩ (fun _ : Fin (b+a) => .rv)
      {w | ∃ u : F.rowDomain z, w = join b a u.val (e u).val} := by
    convert joinedRelationRow_definable H z using 1
    ext w
    change (∃ u : F.rowDomain z, w = join b a u.val (e u).val) ↔
      Fin.append (Fin.append z (w ∘ headIndex b a)) (w ∘ tailIndex b a) ∈ H.val
    rw [he]
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨u,(funext (join_head b a _ _)).symm,(funext (join_tail b a _ _)).symm⟩
    · rintro ⟨u,hu,hv'⟩
      refine ⟨u,?_⟩
      calc
        w = join b a (w ∘ headIndex b a) (w ∘ tailIndex b a) := (join_reconstruct b a w).symm
        _ = _ := by rw [←hu,←hv']
  exact rawEquivalenceBijection (F.rowDomain z) (G.rowDomain z) (F.row_domain_definable z)
    (G.row_domain_definable z) e hg

end DiamondIntegral.Section5
