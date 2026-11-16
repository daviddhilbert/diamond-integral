import «section 6».UnaryCoreCapture

/-! Prescribed original unary cores with actual original-base endpoint
maps. The radii are values of those endpoints. Source membership and
uniqueness of the centre in each separated core are proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}

structure UnaryCorePlan (A : DefSet (rawMixedSpace (M := M) 1 r) S) where
  centres : DefSet (rawMixedSpace (M := M) 1 r) S
  subset : centres.carrier ⊆ A.carrier
  finite_vf : (Prod.fst '' centres.carrier).Finite
  offset : Map centres (DefSet.univ (rawVFSpace 1) S)
  offset_nonzero : ∀ p : centres,(offset p).val 0≠0
  source_bound : ∀ p : centres,vfValue (p.val.1 0)<vfValue ((offset p).val 0)
  separated : ∀ p q : centres,p≠q → Disjoint
    (unaryTaggedDisc p.val (finiteValue ((offset p).val 0) (offset_nonzero p)))
    (unaryTaggedDisc q.val (finiteValue ((offset q).val 0) (offset_nonzero q)))

namespace UnaryCorePlan
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def centre (P : UnaryCorePlan A) (p : P.centres) : A := ⟨p.val,P.subset p.property⟩

def centreMap (P : UnaryCorePlan A) : Map P.centres A := Map.inclusion P.subset

def radius (P : UnaryCorePlan A) (p : P.centres) : Gamma M :=
  finiteValue ((P.offset p).val 0) (P.offset_nonzero p)

def disc (P : UnaryCorePlan A) (p : P.centres) : Set (Mixed M 1 r) := unaryTaggedDisc p.val (P.radius p)

theorem centre_nonzero (P : UnaryCorePlan A) (p : P.centres) : p.val.1 0≠0 := by
  intro hz
  have h := P.source_bound p
  rw [hz,value_zero] at h
  exact (not_lt_of_ge (Values.le_infinity _)) h

theorem disc_subset (P : UnaryCorePlan A) (hA : IsRVPullback A.carrier) (p : P.centres) :
    P.disc p ⊆ A.carrier :=
  UnaryCoreChart.source_disc_subset (p := P.centre p) (γ := P.radius p) hA
    (P.centre_nonzero p) (P.source_bound p).le

theorem centre_mem_disc (P : UnaryCorePlan A) (p : P.centres) : p.val ∈ P.disc p :=
  unaryTaggedDisc_centre_mem p.val (P.radius p)

theorem centre_unique_in_disc (P : UnaryCorePlan A) (p q : P.centres) (hp : p.val ∈ P.disc q) : p=q := by
  by_contra hne
  have hDis : Disjoint (P.disc p) (P.disc q) := P.separated p q hne
  exact Set.disjoint_left.mp hDis (P.centre_mem_disc p) hp

end UnaryCorePlan
end DiamondIntegral.Section6
