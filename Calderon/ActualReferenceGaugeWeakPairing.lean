import Calderon.ActualReferenceGaugeNativeEnergy
import Calderon.NativeContinuousCoefficientOrthogonalEnergy

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-actual-gauge-pairing-v006.md. Literal weighted pairing of SAME W. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError NativeHarmonicH1LiftCompletion NativeHalfSmoothMultiplier SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData

theorem referenceGaugeNativeEnergy_memLp
    (hg : IsAdmissibleMetric g) (p : ℝ × (R3 × ℝ)) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand
      (referenceExponentialGauge g L Φ p x • a (p,x)) (0 : R3) 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  apply memLp_nativeEnergyIntegrand_of_continuous
  · exact (contDiff_referenceExponentialGauge
      g L Φ hg y0 B ε C ρ H a w hData p).continuous.smul
        (continuous_referenceNativePrincipal g L y0 Φ B ε C ρ H a w hData p)
  · exact continuous_const
  · exact continuous_const

include hData in
theorem referenceGaugeNativeEnergy_comm
    (p : ℝ × (R3 × ℝ)) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0 u v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0 v u := by
  apply TauCeti.PDE.energyFormH1_comm_of_isSymm_ae
  exact Filter.Eventually.of_forall (fun x =>
    (referencePrincipalCoefficient_isSymm g L y0 Φ B ε C ρ H a w hData p x).smul _)

include hData in
theorem referenceWeakHalfLiftFamily_affine_difference_mem_zero
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2 : ℝ)) :
    harmonicFirstOrderLiftCompletion hF f -
      referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let hc := referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p
  have hn := nativeWeakHalfLift_affine_difference
    (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 hc hF f
  have he := congrArg (fun W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 =>
    harmonicFirstOrderLiftCompletion hF f - W f)
    (referenceWeakHalfLiftFamily_eq_nativeWeakHalfLift
      g L y0 Φ B ε C ρ H a w hData hcalc hF p hc)
  exact Eq.mp (congrArg (fun v : BallH1 =>
    v ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) he.symm) hn

theorem referenceGaugeNativeEnergy_test_eq_weakLift
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f z : SphereSobolev (1/2 : ℝ)) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
      (harmonicFirstOrderLiftCompletion hF z) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p z) := by
  let W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
  let T : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 := harmonicFirstOrderLiftCompletion hF
  let hc := referenceGaugeNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData hg p
  let E : BallH1 →L[ℝ] StrongDual ℝ BallH1 := TauCeti.PDE.energyFormH1L hc
  have hval (u v : BallH1) : E u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0 u v :=
    TauCeti.PDE.energyFormH1L_apply hc u v
  have hz : T z-W z ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceWeakHalfLiftFamily_affine_difference_mem_zero g L y0 Φ B ε C ρ H a w hData hcalc hF p z
  have hZero := referenceWeakHalfLiftFamily_weighted_energy_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF p hWeak f ⟨T z-W z,hz⟩
  have hLinear : E (W f) (T z-W z) = E (W f) (T z)-E (W f) (W z) :=
    (E (W f)).map_sub (T z) (W z)
  have hEzero : E (W f) (T z-W z) = 0 := (hval _ _).trans hZero
  have hEqual : E (W f) (T z) = E (W f) (W z) := sub_eq_zero.mp (hLinear.symm.trans hEzero)
  exact (hval _ _).symm.trans (hEqual.trans (hval _ _))

theorem referenceGaugeNativeEnergy_boundary_pairing_comm
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f z : SphereSobolev (1/2 : ℝ)) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
      (harmonicFirstOrderLiftCompletion hF z) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p z)
      (harmonicFirstOrderLiftCompletion hF f) :=
  (referenceGaugeNativeEnergy_test_eq_weakLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF p hWeak f z).trans
    ((referenceGaugeNativeEnergy_comm g L y0 Φ B ε C ρ H a w hData p _ _).trans
      (referenceGaugeNativeEnergy_test_eq_weakLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF p hWeak z f).symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNativeEnergy_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNativeEnergy_comm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakHalfLiftFamily_affine_difference_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNativeEnergy_test_eq_weakLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNativeEnergy_boundary_pairing_comm
