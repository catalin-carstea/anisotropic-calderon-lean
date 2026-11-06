import Calderon.ActualLowerUSAdjointZeroPolynomial
import Calderon.ActualFiniteHarmonicModelQuadraticAngularAdjoint
import Calderon.ActualPerturbedModelSupport

/-! Author-support GPT-6.1 Sol. Before-code ../gained-jq-upfront.md.
Actual finite true adjoints of the restricted lower-only J dictionary.
Raising occurs only in a genuine finite adjoint test. No E self-adjointness.
Source-only pending Root's native qualification; no compilation by author. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner)

/-- True finite angular adjoint of identity, minus-rotation, degree, lowering. -/
def lowerCoreAngularGeneratorAdjoint : LowerCoreAngularGeneratorIndex →
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD)
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl (Sum.inl (b,c))) => coreRotation hO hD b c
  | Sum.inr (Sum.inl (Sum.inr _)) => coreDegree hO hD
  | Sum.inr (Sum.inr a) => coreRaising hO hD hF a

lemma hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator
    (i : LowerCoreAngularGeneratorIndex) (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD (lowerCoreAngularGenerator hO hD hF i)
      (lowerCoreAngularGeneratorAdjoint hO hD hF i) (coreAngularGeneratorBound hO hD) x := by
  rcases i with u | ((bc | u) | a)
  · cases u
    exact hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF
      (Sum.inr (Sum.inr (Sum.inr false))) x
  · have hRot : HasCoreAngularFirstOrderBounds hO hD
        (coreRotation hO hD bc.1 bc.2) (-coreRotation hO hD bc.1 bc.2)
        (coreAngularGeneratorBound hO hD) x :=
      hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF
        (Sum.inr (Sum.inr (Sum.inl bc))) x
    have hh := hasCoreAngularFirstOrderBounds_neg hO hD
      (coreRotation hO hD bc.1 bc.2) (-coreRotation hO hD bc.1 bc.2)
      (coreAngularGeneratorBound hO hD) x hRot
    have hNeg : -(-coreRotation hO hD bc.1 bc.2) = coreRotation hO hD bc.1 bc.2 := by
      apply LinearMap.ext
      intro F
      apply Subtype.ext
      funext y
      simp only [LinearMap.neg_apply,Submodule.coe_neg,Pi.neg_apply,neg_neg]
    rw [hNeg] at hh
    exact hh
  · cases u
    exact hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF
      (Sum.inr (Sum.inr (Sum.inr true))) x
  · exact hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (Sum.inl a) x

/-- Ordered quadratic dictionary; its true adjoint reverses the two factors. -/
def lowerQuadraticWord (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  lowerCoreAngularGenerator hO hD hF ij.1 * lowerCoreAngularGenerator hO hD hF ij.2

def lowerQuadraticWordAdjoint (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  lowerCoreAngularGeneratorAdjoint hO hD hF ij.2 * lowerCoreAngularGeneratorAdjoint hO hD hF ij.1

lemma lowerQuadraticWord_inner_adjoint
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪(lowerQuadraticWord hO hD hF ij F).val x,G.val x⟫_ℝ =
      ⟪F.val x,(lowerQuadraticWordAdjoint hO hD hF ij G).val x⟫_ℝ := by
  exact coreAngular_product_inner_adjoint hO hD _ _ _ _ _ _ x
    (hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator hO hD hF ij.1 x)
    (hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator hO hD hF ij.2 x) F G

/-- An everywhere pointwise angular adjunction implies support locality. -/
lemma finiteCoreSupportPreserving_of_pointwise_adjoint
    (A S : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hAdj : ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ x : R3,
      ⟪(A F).val x,G.val x⟫_ℝ = ⟪F.val x,(S G).val x⟫_ℝ) :
    FiniteCoreSupportPreserving hO hD A := by
  intro F
  apply closure_mono
  intro x hx hz
  apply hx
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hh := hAdj F (A F) x
  rw [hz,inner_zero_left] at hh
  exact hh

lemma finiteCoreSupportPreserving_lowerQuadraticWord
    (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
    FiniteCoreSupportPreserving hO hD (lowerQuadraticWord hO hD hF ij) :=
  finiteCoreSupportPreserving_of_pointwise_adjoint hO hD _ _
    (lowerQuadraticWord_inner_adjoint hO hD hF ij)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
