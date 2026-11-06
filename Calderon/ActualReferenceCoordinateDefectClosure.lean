import Calderon.NativeCoordinateHarmonicDefectCompletion
import Calderon.NativeCoordinateEnergyCancellation
import Calderon.ActualReferenceNativeWeakHalfLift

set_option autoImplicit false
noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHalfSmoothMultiplier

/-! Upfront expansion: EXPANSION-actual-coordinate-defect-closure-joint-v001.md. -/

theorem coordinateSmoothDatum_eq_smoothPolynomialData (k : Fin 3) :
    coordinateSmoothDatum k = smoothPolynomialData (X k) := by
  apply Subtype.ext
  funext x
  simp only [coordinateSmoothDatum,smoothPolynomialData,eval_X,polynomialCoordinateMap_apply]

theorem nativeWeakHalfLift_coordinate_defect_mem_zero_of_datum_eq
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) (m : SmoothData) (hmData : m = smoothPolynomialData (X k))
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (f : SphereSobolev (1/2 : ℝ)) :
    nativeWeakHalfLift a b c hcoeff hF (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) -
      TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
        m.1 m.2 hM hm hg (nativeWeakHalfLift a b c hcoeff hF f) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  subst m
  exact nativeWeakHalfLift_coordinate_defect_mem_zero hF hO hD τ0 k hM hm hg a b c hcoeff f

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceCoordinateWeakDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
  (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p).comp
    (nativeHalfSmoothMulL hF hO hD τ0 (coordinateSmoothDatum k) hM hm hg) -
  (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
    (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg).comp
    (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)

theorem referenceCoordinateWeakDefectFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2 : ℝ)) :
    referenceCoordinateWeakDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k hM hm hg p f =
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
      (nativeHalfSmoothMulL hF hO hD τ0 (coordinateSmoothDatum k) hM hm hg f) -
    TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) := rfl

theorem referenceCoordinateWeakDefectFamily_mem_zero
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2 : ℝ)) :
    referenceCoordinateWeakDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k hM hm hg p f ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let hcoeff := referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p
  have hW := referenceWeakHalfLiftFamily_eq_nativeWeakHalfLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hcoeff
  let T := nativeHalfSmoothMulL hF hO hD τ0 (coordinateSmoothDatum k) hM hm hg
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg
  have he := congrArg (fun W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 => W (T f)-S (W f)) hW
  have hz := nativeWeakHalfLift_coordinate_defect_mem_zero_of_datum_eq
    hF hO hD τ0 k (coordinateSmoothDatum k) (coordinateSmoothDatum_eq_smoothPolynomialData k)
    hM hm hg (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    0 hcoeff f
  rw [referenceCoordinateWeakDefectFamily_apply]
  change referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p (T f)-
    S (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) ∈ _
  exact he.symm ▸ hz

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
