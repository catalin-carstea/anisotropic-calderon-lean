import Calderon.ActualReferenceExponentialGauge
import Calderon.NativeGradientGaugeEnergy
import Calderon.ActualReferenceCoordinateDefectGain

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-actual-gauge-native-energy-v005.md. SAME original weak lift;
no new weighted inverse or boundary pairing premise. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator NativeHalfSmoothMultiplier SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData in
theorem referencePrincipalCoefficient_isSymm (p : ℝ × (R3 × ℝ)) (z : R3) :
    (a (p,z)).IsSymm := by
  have ha := hData.2.2.2.2.1 (p,z)
  rcases hData.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  rw [ha]
  exact (hPos (p,z)).isHermitian.isSymm.inv.smul (w (p,z))

def referenceExponentialGaugeData (hg : IsAdmissibleMetric g) (p : ℝ × (R3 × ℝ)) :
    SmoothData :=
  ⟨referenceExponentialGauge g L Φ p,
    contDiff_referenceExponentialGauge g L Φ hg y0 B ε C ρ H a w hData p⟩

theorem exists_referenceExponentialGauge_ball_bound (hg : IsAdmissibleMetric g)
    (p : ℝ × (R3 × ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ x ∈ (ballOpens : Set R3), |(referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).1 x| ≤ M) ∧
      (∀ x ∈ (ballOpens : Set R3), ‖gradient (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).1 x‖ ≤ M) :=
  exists_smooth_ball_multiplier_bound (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p)

include hData in
theorem referenceExponentialGauge_native_coordinate_identity
    (hg : IsAdmissibleMetric g) (p : ℝ × (R3 × ℝ)) (z : R3) (j : Fin 3) :
    referenceExponentialGauge g L Φ p z * conformalReferenceWeightedFramedDrift g L Φ H w (p,z) j +
      ∑ i : Fin 3, a (p,z) i j * (gradient (referenceExponentialGauge g L Φ p) z) i = 0 := by
  have hv := referenceExponentialGauge_weightedDrift_identity
    g L Φ hg y0 B ε C ρ H a w hData p z
  have hc := congrArg (fun v : R3 => v j) hv
  let Z : R3 := gradient (referenceExponentialGauge g L Φ p) z
  change referenceExponentialGauge g L Φ p z *
    conformalReferenceWeightedFramedDrift g L Φ H w (p,z) j +
    (Matrix.mulVec (a (p,z)) (fun i => Z i)) j = 0 at hc
  simp only [Matrix.mulVec, dotProduct, Z] at hc
  have hs := referencePrincipalCoefficient_isSymm g L y0 Φ B ε C ρ H a w hData p z
  have he : (∑ i : Fin 3, a (p,z) j i * (gradient (referenceExponentialGauge g L Φ p) z) i) =
      ∑ i : Fin 3, a (p,z) i j * (gradient (referenceExponentialGauge g L Φ p) z) i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs.apply i j]
  exact (congrArg (fun t : ℝ => referenceExponentialGauge g L Φ p z *
    conformalReferenceWeightedFramedDrift g L Φ H w (p,z) j + t) he).symm.trans hc

theorem referenceEnergy_exponentialGauge
    (hg : IsAdmissibleMetric g) (p : ℝ × (R3 × ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).1 x| ≤ M)
    (hgrad : ∀ x ∈ (ballOpens : Set R3), ‖gradient (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).1 x‖ ≤ M)
    (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 u
      (TauCeti.W1p.contDiffSMulL
        (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).1
        (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).2 hM hm hgrad v) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0 u v := by
  apply nativeEnergy_gradient_gauge
  intro x hx j
  exact referenceExponentialGauge_native_coordinate_identity
    g L y0 Φ B ε C ρ H a w hData hg p x j

theorem referenceExponentialGauge_zero_test_mem
    (hg : IsAdmissibleMetric g) (p : ℝ × (R3 × ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).1 x| ≤ M)
    (hgrad : ∀ x ∈ (ballOpens : Set R3), ‖gradient (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).1 x‖ ≤ M)
    (v : BallH1Zero) :
    TauCeti.W1p.contDiffSMulL
      (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).1
      (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).2 hM hm hgrad (v : BallH1) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule
    (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p).2 hM hm hgrad v.property

theorem referenceWeakHalfLiftFamily_weighted_energy_of_isInvertible
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (v : BallH1) = 0 := by
  obtain ⟨M,hM,hm,hgrad⟩ := exists_referenceExponentialGauge_ball_bound
    g L y0 Φ B ε C ρ H a w hData hg p
  let m := referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hgrad
  have hSv : S (v : BallH1) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceExponentialGauge_zero_test_mem g L y0 Φ B ε C ρ H a w hData hg p hM hm hgrad v
  have hZero := referenceWeakHalfLiftFamily_weak_energy_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak f ⟨S (v : BallH1),hSv⟩
  have hEnergy := referenceEnergy_exponentialGauge
    g L y0 Φ B ε C ρ H a w hData hg p hM hm hgrad
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (v : BallH1)
  exact hEnergy.symm.trans hZero

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePrincipalCoefficient_isSymm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceExponentialGaugeData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceExponentialGauge_ball_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceExponentialGauge_native_coordinate_identity
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceEnergy_exponentialGauge
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceExponentialGauge_zero_test_mem
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakHalfLiftFamily_weighted_energy_of_isInvertible
