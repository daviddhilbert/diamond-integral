import «section 5».NewtonPuiseuxAlgClosed
import «section 5».PuiseuxField

/-! The local concrete field is exactly the bounded-denominator Hahn
subfield in the checked Newton–Puiseux proof, not an abstract closure.
Transfer algebraic closedness along the identity on Hahn series. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
variable (K : Type) [Field K]

theorem laurentToRational_eq_newton (n : ℕ+) :
    laurentToRational (k := K) n.pos = LaurentSeries.toHahn K n := rfl

theorem puiseuxSubfield_eq_newton : puiseuxSubfield K = _root_.PuiseuxSeries.subfield K := by
  ext x
  rw [_root_.PuiseuxSeries.mem_subfield_iff]
  constructor
  · rintro ⟨n,hn,hx⟩
    exact ⟨⟨n,hn⟩,hx⟩
  · rintro ⟨n,hx⟩
    exact ⟨n.val,n.pos,hx⟩

def puiseuxNewtonEquiv : PuiseuxSeries K ≃+* _root_.PuiseuxSeries K :=
  RingEquiv.subfieldCongr (puiseuxSubfield_eq_newton K)

theorem puiseuxNewtonEquiv_coe (x : PuiseuxSeries K) :
    (_root_.PuiseuxSeries.subfield K).subtype (puiseuxNewtonEquiv K x) = (x : HahnSeries ℚ K) := rfl

theorem puiseuxAlgebraicallyClosed [IsAlgClosed K] [CharZero K] : IsAlgClosed (PuiseuxSeries K) :=
  IsAlgClosed.of_ringEquiv (_root_.PuiseuxSeries K) (PuiseuxSeries K) (puiseuxNewtonEquiv K).symm

end DiamondIntegral.Section5
