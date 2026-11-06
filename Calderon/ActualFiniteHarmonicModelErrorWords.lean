import Calderon.ActualFiniteHarmonicModelError
import Calderon.ActualModelCommutatorWords

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev nativeRingCoreFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeRingCoreFunction

def nativeFullErrorExpression
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  let U := nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let Udag := nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let T := nativeT hO hD hF g1 hg1 L lam δ R p hδ hR
  let Tdag := nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR
  let Z := nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR
  let Zdag := nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR
  2*commutator Tdag U + 2*commutator Udag T + commutator Udag U -
    2*(U*Z+Zdag*Udag)

def nativeReducedErrorExpression
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  let U := nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let Udag := nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let T := nativeT hO hD hF g1 hg1 L lam δ R p hδ hR
  let Tdag := nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR
  let Z := nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR
  let Zdag := nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR
  commutator (2*(Tdag-T)+(Udag-U)) U +
    2*commutator (Udag-U) T - 2*(U*Z+Zdag*Udag)

lemma nativeEndProduct_apply
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (A*B) F x = A (B F) x := by
  rfl

lemma nativeEndCommutator_apply
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    commutator A B F x = A (B F) x - B (A F) x := by
  simp only [ActualModelCommutatorWords.commutator, LinearMap.sub_apply, Module.End.mul_apply,
    Submodule.coe_sub, Pi.sub_apply]

theorem nativeFullErrorExpression_eq_reduced
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR =
      nativeReducedErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  unfold nativeFullErrorExpression nativeReducedErrorExpression
  exact ActualModelCommutatorWords.full_error_expression_reduction
    (nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativeT hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR)

lemma nativeFullErrorExpression_apply_eq_reduced
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x =
      nativeReducedErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  exact congrArg
    (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => A F x)
    (nativeFullErrorExpression_eq_reduced hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
