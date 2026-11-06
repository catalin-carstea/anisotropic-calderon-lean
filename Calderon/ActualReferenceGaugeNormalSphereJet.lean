import Calderon.ActualReferenceGaugeBoundaryCoefficientFamilies
import Calderon.LocalSphereCurrying

/-! Sup-norm scalar boundary jet from the joint scalar field and compact sphere
currying. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  MetricVolume SphereHarmonic

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

def referenceGaugeNormalSphereValueFamily (p : ℝ × (R3 × ℝ)) : C(UnitSphere,ℝ) :=
  smoothSphereValue (coefficientSmoothData
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p))

theorem referenceGaugeNormalSphereValueFamily_apply
    (p : ℝ × (R3 × ℝ)) (x : UnitSphere) :
    referenceGaugeNormalSphereValueFamily g L Φ y0 B ε C ρ H a w hData hg p x =
      referenceGaugeNormalCoefficient g L Φ a (p,x.val) := by
  change coefficientValue 2
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p) x.val = _
  exact coefficientValue_referenceGaugeNormalCoefficientJetsFamily
    g L Φ y0 B ε C ρ H a w hData hg 2 p x.val

attribute [local irreducible] referenceGaugeNormalSphereValueFamily

theorem contDiff_referenceGaugeNormalSphereValueFamily :
    ContDiff ℝ ∞ (referenceGaugeNormalSphereValueFamily g L Φ y0 B ε C ρ H a w hData hg) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact contDiffAt_sphereFamily_of_joint_on_open
    (referenceGaugeNormalCoefficient g L Φ a) Set.univ isOpen_univ
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg).contDiffOn
    (referenceGaugeNormalSphereValueFamily g L Φ y0 B ε C ρ H a w hData hg)
    (fun t _ x => referenceGaugeNormalSphereValueFamily_apply
      g L Φ y0 B ε C ρ H a w hData hg t x) p (fun _ => Set.mem_univ _)

theorem referenceGaugeNormalSphereValueFamily_zero_radial_jet
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) :
    referenceGaugeNormalSphereValueFamily g L Φ y0 B ε C ρ H a w hData hg (q,(y,0)) = 1 ∧
    HasDerivAt (fun r : ℝ => referenceGaugeNormalSphereValueFamily
      g L Φ y0 B ε C ρ H a w hData hg (q,(y,r)))
      (∑ i : Fin 3, (referenceCenterDrift g L q y i) • sphereCoordinate i) 0 := by
  let F : ℝ → C(UnitSphere,ℝ) := fun r => referenceGaugeNormalSphereValueFamily
    g L Φ y0 B ε C ρ H a w hData hg (q,(y,r))
  have hSlice : ContDiff ℝ ∞ (fun r : ℝ => (q,(y,r))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_referenceGaugeNormalSphereValueFamily g L Φ y0 B ε C ρ H a w hData hg).comp hSlice
  have hd : HasDerivAt F (deriv F 0) 0 := (hF.differentiable (by simp) 0).hasDerivAt
  have hValue (x : UnitSphere) : F 0 x = 1 :=
    (referenceGaugeNormalSphereValueFamily_apply g L Φ y0 B ε C ρ H a w hData hg (q,(y,0)) x).trans
      (referenceGaugeNormalCoefficient_zero_radial_jet g L Φ y0 B ε C ρ H a w hData q hq y hy x).1
  have hDerivative : deriv F 0 =
      ∑ i : Fin 3, (referenceCenterDrift g L q y i) • sphereCoordinate i := by
    apply ContinuousMap.ext
    intro x
    have hEval := (ContinuousMap.evalCLM ℝ x : C(UnitSphere,ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    have hCurve : (fun r => F r x) = (fun r : ℝ =>
        referenceGaugeNormalCoefficient g L Φ a ((q,(y,r)),x.val)) := by
      funext r
      exact referenceGaugeNormalSphereValueFamily_apply g L Φ y0 B ε C ρ H a w hData hg (q,(y,r)) x
    change HasDerivAt (fun r => F r x) (deriv F 0 x) 0 at hEval
    rw [hCurve] at hEval
    have hInner := hEval.unique
      (referenceGaugeNormalCoefficient_zero_radial_jet g L Φ y0 B ε C ρ H a w hData q hq y hy x).2
    have hSum : inner ℝ (referenceCenterDrift g L q y) x.val =
        (∑ i : Fin 3, (referenceCenterDrift g L q y i) • sphereCoordinate i) x := by
      simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
      change inner ℝ (referenceCenterDrift g L q y) x.val =
        ∑ i : Fin 3, (referenceCenterDrift g L q y i) * x.val i
      simp only [PiLp.inner_apply,Real.inner_apply,mul_comm]
    exact hInner.trans hSum
  constructor
  · exact ContinuousMap.ext hValue
  · rw [hDerivative] at hd
    exact hd

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalSphereValueFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalSphereValueFamily_apply
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeNormalSphereValueFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalSphereValueFamily_zero_radial_jet
