import Calderon.NativeSmoothCoordinateDerivative
import Calderon.OrdinaryWeightedDriftOperator
/-! Source-only author C5 calculus stage. Full exact native realization
derivation and interfaces were sealed first. No physical harmonic/kernel
premise or full moving-trace topology is introduced. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume

def coefficientProductData (k : ℕ) (F : SmoothCoefficientJets (k+1))
    (f : SmoothData) : SmoothData :=
  ⟨fun x => coefficientValue (k+1) F x * f.1 x,
    (contDiff_coefficientValue (k+1) F).mul f.2⟩

theorem coefficientMultiplier_smoothBallSobolev
    (hcalc : FixedSobolevCalculus) (k : ℕ) (F : SmoothCoefficientJets (k+1))
    (f : SmoothData) :
    coefficientMultiplier hcalc k F (smoothBallSobolev k f) =
      smoothBallSobolev k (coefficientProductData k F f) := by
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F (smoothBallSobolev k f),
    value_smoothBallSobolev_ae k f,
    value_smoothBallSobolev_ae k (coefficientProductData k F f)] with x hM hF hP
  rw [hM,hF,hP]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

theorem ordinaryPrincipalL_smoothBallSobolev_value_ae
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F : SmoothCoefficientMatrix (s+2))
    (f : SmoothData) :
    TauCeti.Wkp.value s (ordinaryPrincipalL hcalc s F (smoothBallSobolev (s+2) f))
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => -∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun y => coefficientValue (s+2) (F i j) y *
          fderiv ℝ f.1 y (coordinateVector j)) x (coordinateVector i) := by
  let T (i j : Fin 3) : BallSobolev s := unitBallCoordinateDerivativeL hcalc s i
    (coefficientMultiplier hcalc (s+1) (F i j)
      (unitBallCoordinateDerivativeL hcalc (s+1) j (smoothBallSobolev (s+2) f)))
  let D (i j : Fin 3) : SmoothData := smoothCoordinateDerivative
    (coefficientProductData (s+1) (F i j) (smoothCoordinateDerivative f j)) i
  have hT (i j : Fin 3) : T i j = smoothBallSobolev s (D i j) := by
    dsimp only [T,D]
    rw [unitBallCoordinateDerivativeL_smoothBallSobolev,
      coefficientMultiplier_smoothBallSobolev,
      unitBallCoordinateDerivativeL_smoothBallSobolev]
  have hTv (i j : Fin 3) : TauCeti.Wkp.value s (T i j)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => fderiv ℝ (fun y => coefficientValue (s+2) (F i j) y *
        fderiv ℝ f.1 y (coordinateVector j)) x (coordinateVector i) := by
    rw [hT]
    exact value_smoothBallSobolev_ae s (D i j)
  rw [ordinaryPrincipalL_apply]
  change (TauCeti.Wkp.valueL s) (-∑ i : Fin 3, ∑ j : Fin 3, T i j) =ᵐ[_] _
  simp only [map_neg,map_sum,TauCeti.Wkp.valueL_apply]
  exact (Lp.coeFn_neg _).trans
    (((Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun i _ =>
      (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun j _ => hTv i j))))).neg)

theorem ordinaryStrongDriftFamily_smoothBallSobolev_value_ae
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ) (f : SmoothData) :
    TauCeti.Wkp.value s
      (ordinaryStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p
        (smoothBallSobolev (s+2) f))
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => (-∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun y => a (p,y) i j * fderiv ℝ f.1 y (coordinateVector j)) x
          (coordinateVector i)) + inner ℝ (weightedDriftSlice w b L p x) (gradient f.1 x) := by
  let F := commonSupportMatrixFamily (s+2) a ha K hK hza p
  let E := smoothBallSobolev (s+2) f
  have hCF (i j : Fin 3) : coefficientValue (s+2) (F i j) = fun x => a (p,x) i j := by
    funext x
    exact congrArg (fun M : R3 → Matrix (Fin 3) (Fin 3) ℝ => M x i j)
      (coefficientMatrixField_commonSupportMatrixFamily (s+2) a ha K hK hza p)
  have hP := ordinaryPrincipalL_smoothBallSobolev_value_ae hcalc s F f
  simp_rw [hCF] at hP
  have hD : TauCeti.Wkp.value s
      (ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p E)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => inner ℝ (weightedDriftSlice w b L p x) (gradient f.1 x) := by
    have hd := supportedDriftL_value_inner_ae hcalc 0 (weightedDriftSlice w b L p)
      (contDiff_weightedDriftSlice w hw b hb L p) K hK
      (weightedDriftSlice_support w b L p K hzw) (TauCeti.Wkp.firstOrder (s+1) E)
    simp only [TauCeti.Wkp.value_zero,TauCeti.Wkp.firstOrder_zero] at hd
    rw [← ordinaryWeightedDriftL_value_eq hcalc s w hw b hb K hK hzw L p E] at hd
    change TauCeti.Wkp.value s
      (ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p E)
      =ᵐ[_] fun x => inner ℝ (weightedDriftSlice w b L p x)
        (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder (s+1) (smoothBallSobolev (s+2) f)) x) at hd
    rw [firstOrder_smoothBallSobolev] at hd
    filter_upwards [hd,gradient_smoothSobolev_ae f] with x hx hgrad
    rw [hx,hgrad]
  change (TauCeti.Wkp.valueL s)
    (ordinaryPrincipalL hcalc s F E + ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p E)
      =ᵐ[_] _
  rw [map_add]
  exact (Lp.coeFn_add _ _).trans (hP.add hD)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
